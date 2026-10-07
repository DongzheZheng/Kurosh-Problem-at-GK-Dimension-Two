#!/usr/bin/env python3
"""Check the published Lean source manifest without invoking Lean or Lake."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
LEAN_VERSION = "4.29.0"
MATHLIB_COMMIT = "8a178386ffc0f5fef0b77738bb5449d50efeea95"
MANIFEST = "verification/source-manifest.json"
IGNORED_DIRECTORIES = {".git", ".lake", "__pycache__"}
BUILD_SUFFIXES = {".olean", ".ilean", ".o", ".trace"}
PRIVATE_ARTIFACT_NAMES = {"server_latest.json", "server_report.json", "server_certificates"}


class ManifestError(ValueError):
    """A source manifest or source tree failed validation."""


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def repository_files(root: Path) -> list[Path]:
    """List files outside local Git, Lake, and Python cache directories."""
    files: list[Path] = []
    def traversal_error(error: OSError) -> None:
        raise ManifestError("Cannot inspect the repository source tree.") from error

    for directory, directories, names in os.walk(root, followlinks=False, onerror=traversal_error):
        directories[:] = sorted(d for d in directories if d not in IGNORED_DIRECTORIES)
        for name in directories:
            path = Path(directory) / name
            relative = path.relative_to(root).as_posix()
            if path.is_symlink():
                raise ManifestError(f"Unexpected directory symlink: {relative}.")
            if name in PRIVATE_ARTIFACT_NAMES:
                raise ManifestError(f"Unexpected private artifact directory: {relative}.")
        for name in sorted(names):
            files.append(Path(directory) / name)
    return files


def checked_sources(root: Path = ROOT) -> dict[str, str]:
    """Return the manifest after checking its metadata, file set, and hashes."""
    manifest_path = root / MANIFEST
    if not manifest_path.is_file() or manifest_path.is_symlink():
        raise ManifestError(f"Missing {MANIFEST}.")

    def unique_object(pairs: list[tuple]) -> dict:
        value = {}
        for key, item in pairs:
            if key in value:
                raise ManifestError(f"Duplicate manifest key: {key!r}.")
            value[key] = item
        return value

    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"), object_pairs_hook=unique_object)
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise ManifestError(f"Cannot read {MANIFEST}: {type(error).__name__}.") from error
    if not isinstance(manifest, dict):
        raise ManifestError("The manifest must be a JSON object.")
    if manifest.get("lean_version") != LEAN_VERSION:
        raise ManifestError(f"The manifest must specify Lean {LEAN_VERSION}.")
    if manifest.get("mathlib_commit") != MATHLIB_COMMIT:
        raise ManifestError("The manifest does not specify the pinned mathlib commit.")
    source_hashes = manifest.get("source_hashes")
    if not isinstance(source_hashes, dict) or not source_hashes:
        raise ManifestError("The manifest must contain a nonempty source_hashes object.")
    for relative, digest in source_hashes.items():
        if not isinstance(relative, str):
            raise ManifestError("Manifest source paths must be strings.")
        path = PurePosixPath(relative)
        if (
            path.is_absolute()
            or ".." in path.parts
            or "\\" in relative
            or str(path) != relative
            or path.suffix != ".lean"
            or any(part in IGNORED_DIRECTORIES for part in path.parts)
        ):
            raise ManifestError(f"Invalid source path: {relative!r}.")
        if not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
            raise ManifestError(f"Invalid SHA-256 digest for {relative}.")

    files = repository_files(root)
    artifacts = sorted(
        str(path.relative_to(root))
        for path in files
        if path.suffix in BUILD_SUFFIXES or path.name in PRIVATE_ARTIFACT_NAMES
    )
    if artifacts:
        raise ManifestError("Unexpected build or private artifacts: " + ", ".join(artifacts))
    actual = {path.relative_to(root).as_posix() for path in files if path.suffix == ".lean"}
    expected = set(source_hashes)
    missing, extra = sorted(expected - actual), sorted(actual - expected)
    if missing or extra:
        details = []
        if missing:
            details.append("missing sources: " + ", ".join(missing))
        if extra:
            details.append("unlisted sources: " + ", ".join(extra))
        raise ManifestError("Source file set mismatch; " + "; ".join(details))
    root_resolved = root.resolve()
    for relative, expected_hash in sorted(source_hashes.items()):
        source = root / relative
        if source.is_symlink() or not source.resolve().is_relative_to(root_resolved):
            raise ManifestError(f"Source files must be regular repository files: {relative}.")
        try:
            actual_hash = sha256(source)
        except OSError as error:
            raise ManifestError(f"Cannot read source: {relative}.") from error
        if actual_hash != expected_hash:
            raise ManifestError(f"SHA-256 mismatch: {relative}.")
    return dict(sorted(source_hashes.items()))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    try:
        sources = checked_sources()
    except (ManifestError, OSError) as error:
        print(f"Manifest check failed: {error}", file=sys.stderr)
        return 1
    print(f"Manifest verified: {len(sources)} Lean source files; all SHA-256 hashes match.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
