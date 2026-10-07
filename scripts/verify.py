#!/usr/bin/env python3
"""Recompile every published Lean source and audit its axiom dependencies.

Run from a configured checkout with:
    lake env python3 scripts/verify.py

The JSON report records this execution. It is written only after the checks
have run and contains repository-relative paths.
"""

from __future__ import annotations

import argparse
from collections import Counter
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

if __package__:
    from . import check_manifest as manifest_tools
else:
    import check_manifest as manifest_tools

LEAN_VERSION = manifest_tools.LEAN_VERSION
MATHLIB_COMMIT = manifest_tools.MATHLIB_COMMIT
ROOT = manifest_tools.ROOT
ManifestError = manifest_tools.ManifestError
checked_sources = manifest_tools.checked_sources
sha256 = manifest_tools.sha256

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
REQUIRED_ENDPOINTS = {
    "CriticalGK2.Actual.originalField_critical_gk_two_absolute_nil_endpoint",
    "CriticalGK2.Actual.exists_prime_critical_gk_two_absolute_nil",
    "CriticalGK2.Actual.exists_prime_critical_gk_two_absolute_nil_default",
    "CriticalGK2.Actual.exists_unital_critical_gk_two_absolute_algebraic",
    "CriticalGK2.Actual.exists_same_prime_critical_algebra_and_absolute_unitization",
}
REPORT = ROOT / "verification/local-report.json"
BUILD = ROOT / ".lake/build/lib/lean"


class VerificationError(ValueError):
    """A precondition or proof audit failed."""


def lean_code(source: str) -> str:
    """Mask Lean comments and string/character literals while preserving lines.

    Block comments nest in Lean. Keeping line positions makes scan failures
    point to the source declaration rather than to documentation text.
    """
    result = list(source)
    index = 0
    length = len(source)

    def mask(start: int, end: int) -> None:
        for position in range(start, end):
            if source[position] != "\n":
                result[position] = " "

    while index < length:
        if source.startswith("/-", index):
            start, depth = index, 1
            index += 2
            while index < length and depth:
                if source.startswith("/-", index):
                    depth += 1
                    index += 2
                elif source.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            if depth:
                raise VerificationError("Unterminated Lean block comment.")
            mask(start, index)
        elif source.startswith("--", index):
            end = source.find("\n", index)
            end = length if end == -1 else end
            mask(index, end)
            index = end
        elif source[index] == '"':
            start = index
            index += 1
            while index < length:
                if source[index] == "\\":
                    index += 2
                elif source[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
            else:
                raise VerificationError("Unterminated Lean string literal.")
            mask(start, min(index, length))
        elif source[index] == "'":
            character = re.match(r"'(?:\\(?:u[0-9a-fA-F]{4}|x[0-9a-fA-F]{2}|.)|[^\\'\n])'", source[index:])
            if character:
                end = index + len(character.group())
                mask(index, end)
                index = end
            else:
                index += 1
        elif source[index] == "«":
            end = source.find("»", index + 1)
            if end == -1:
                raise VerificationError("Unterminated quoted Lean identifier.")
            index = end + 1
        else:
            index += 1
    return "".join(result)


def source_description(relative: str, modules: dict[str, str]) -> dict:
    code = lean_code((ROOT / relative).read_text(encoding="utf-8"))
    forbidden = []
    for match in re.finditer(r"\b(?:sorry|admit|native_decide|unsafe|axiom)\b", code):
        forbidden.append({"token": match.group(), "line": code.count("\n", 0, match.start()) + 1})
    imports = []
    for names in re.findall(r"^\s*(?:public\s+)?import[ \t]+([^\n]+)", code, flags=re.M):
        for module in names.split():
            if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9'.]*", module):
                raise VerificationError(f"Unsupported import syntax in {relative}.")
            if module in modules:
                imports.append(modules[module])
            elif module.startswith("CriticalGK2.") or module == "CriticalGK2" or module == "Verification":
                raise VerificationError(f"Missing project import {module} in {relative}.")
    queries = re.findall(r"#\s*print\s+axioms\s+([A-Za-z_][A-Za-z_0-9'.]*)", code)
    return {"project_imports": sorted(set(imports)), "forbidden_syntax": forbidden, "axiom_queries": queries}


def compile_order(descriptions: dict[str, dict]) -> list[str]:
    states: dict[str, int] = {}
    ordered: list[str] = []

    def visit(relative: str) -> None:
        state = states.get(relative, 0)
        if state == 2:
            return
        if state == 1:
            raise VerificationError(f"Cyclic project imports at {relative}.")
        states[relative] = 1
        for dependency in descriptions[relative]["project_imports"]:
            visit(dependency)
        states[relative] = 2
        ordered.append(relative)

    for relative in sorted(descriptions):
        visit(relative)
    return ordered


def public_diagnostics(text: str) -> str:
    """Keep diagnostic content while removing machine-specific absolute paths."""
    text = text.replace(str(ROOT), ".").replace(str(Path.home()), "<home>")
    text = re.sub(r"(?<![\w.])/(?:[^\s'\"<>])+", "<external-path>", text)
    return re.sub(r"\b[A-Za-z]:[\\/][^\s'\"<>]+", "<external-path>", text)


def axiom_dependencies(diagnostics: str, queries: list[str]) -> list[dict]:
    found: dict[str, list[list[str]]] = {}
    pattern = r"'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
    for match in re.finditer(pattern, diagnostics, flags=re.S):
        names = [] if match.group(2) is None else [name.strip() for name in match.group(2).split(",") if name.strip()]
        found.setdefault(match.group(1), []).append(names)
    missing = Counter(queries) - Counter({name: len(values) for name, values in found.items()})
    if missing:
        raise VerificationError("Missing axiom diagnostics for: " + ", ".join(sorted(missing)))
    audited = []
    for name, values in sorted(found.items()):
        for dependencies in values:
            extra = set(dependencies) - STANDARD_AXIOMS
            if extra:
                raise VerificationError(f"Additional axiom dependencies for {name}: " + ", ".join(sorted(extra)))
            audited.append({"declaration": name, "dependencies": sorted(set(dependencies))})
    return audited


def run_command(arguments: list[str], environment: dict[str, str] | None = None) -> str:
    process = subprocess.run(arguments, cwd=ROOT, env=environment, text=True, capture_output=True, check=False)
    if process.returncode:
        details = public_diagnostics(process.stdout + process.stderr).strip()
        raise VerificationError(f"Command failed: {arguments[0]}." + (" " + details if details else ""))
    return process.stdout.strip()


def verify(timeout: float) -> tuple[dict, bool]:
    sources = checked_sources()
    version = run_command(["lean", "--version"])
    if not version.startswith(f"Lean (version {LEAN_VERSION},"):
        raise VerificationError(f"Expected Lean {LEAN_VERSION}. Run this script under lake env.")
    mathlib = ROOT / ".lake/packages/mathlib"
    if not mathlib.is_dir():
        raise VerificationError("Missing .lake/packages/mathlib; install the pinned Lake dependencies first.")
    commit = run_command(["git", "-C", str(mathlib), "rev-parse", "HEAD"])
    changes = run_command(["git", "-C", str(mathlib), "status", "--porcelain", "--untracked-files=no"])
    if commit != MATHLIB_COMMIT or changes:
        raise VerificationError("mathlib must be at the pinned commit with no tracked changes.")
    modules = {Path(relative).with_suffix("").as_posix().replace("/", "."): relative for relative in sources}
    descriptions = {relative: source_description(relative, modules) for relative in sources}
    source_queries = {name for row in descriptions.values() for name in row["axiom_queries"]}
    if not REQUIRED_ENDPOINTS <= source_queries:
        raise VerificationError("Missing required endpoint queries: " + ", ".join(sorted(REQUIRED_ENDPOINTS - source_queries)))
    order = compile_order(descriptions)
    environment = dict(os.environ)
    lean_paths = [part for part in environment.get("LEAN_PATH", "").split(os.pathsep) if part]
    build_path = str(BUILD)
    if build_path not in lean_paths:
        lean_paths.insert(0, build_path)
    environment["LEAN_PATH"] = os.pathsep.join(lean_paths)
    BUILD.mkdir(parents=True, exist_ok=True)
    for relative in order:
        target = BUILD / Path(relative).with_suffix(".olean")
        target.unlink(missing_ok=True)
    results = []
    passed: set[str] = set()
    audited_endpoints: set[str] = set()
    for number, relative in enumerate(order, start=1):
        print(f"[{number}/{len(order)}] {relative}", flush=True)
        description = descriptions[relative]
        target = BUILD / Path(relative).with_suffix(".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        start = time.monotonic()
        audited = []
        output_hash = None
        compiled = False
        blocked = sorted(set(description["project_imports"]) - passed)
        if sha256(ROOT / relative) != sources[relative]:
            code, diagnostics = 3, "Source changed before compilation."
        elif description["forbidden_syntax"]:
            code, diagnostics = 2, "Forbidden proof syntax detected."
        elif blocked:
            code, diagnostics = 2, "Project imports failed verification: " + ", ".join(blocked)
        else:
            try:
                compiled = True
                process = subprocess.run(["lean", "-o", str(target), relative], cwd=ROOT, env=environment,
                                         text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                         timeout=timeout, check=False)
                code, diagnostics = process.returncode, process.stdout
            except subprocess.TimeoutExpired as error:
                output = error.stdout or ""
                diagnostics = (output.decode(errors="replace") if isinstance(output, bytes) else output)
                diagnostics += "\nCompilation exceeded the configured timeout."
                code = 124
            if sha256(ROOT / relative) != sources[relative]:
                code, diagnostics = 3, diagnostics + "\nSource changed during compilation."
            if code == 0:
                try:
                    audited = axiom_dependencies(diagnostics, description["axiom_queries"])
                    if not target.is_file():
                        raise VerificationError("Lean did not produce the expected object file.")
                except VerificationError as error:
                    code, diagnostics = 4, diagnostics + "\n" + str(error)
                else:
                    output_hash = sha256(target)
                    passed.add(relative)
                    audited_endpoints.update(row["declaration"] for row in audited)
        results.append({
            "file": relative,
            "source_sha256": sources[relative],
            "exit_code": code,
            "seconds": round(time.monotonic() - start, 3),
            "project_imports": description["project_imports"],
            "forbidden_syntax": description["forbidden_syntax"],
            "axiom_queries": audited,
            "diagnostics": public_diagnostics(diagnostics),
            "output_sha256": output_hash,
            "compiler_invoked": compiled,
            "reused": False,
        })
    try:
        unchanged = checked_sources() == sources
    except (ManifestError, OSError):
        unchanged = False
    environment_unchanged = (
        run_command(["git", "-C", str(mathlib), "rev-parse", "HEAD"]) == MATHLIB_COMMIT
        and not run_command(["git", "-C", str(mathlib), "status", "--porcelain", "--untracked-files=no"])
    )
    endpoints_complete = REQUIRED_ENDPOINTS <= audited_endpoints
    all_passed = len(passed) == len(sources) and unchanged and environment_unchanged and endpoints_complete
    report = {
        "schema_version": 1,
        "lean_version": LEAN_VERSION,
        "compiler_version": public_diagnostics(version),
        "mathlib_commit": commit,
        "mathlib_tracked_tree_clean": environment_unchanged,
        "source_manifest_sha256": sha256(ROOT / "verification/source-manifest.json"),
        "sources_unchanged": unchanged,
        "source_count": len(sources),
        "fresh_checked_file_count": sum(row["compiler_invoked"] for row in results),
        "reused_checked_file_count": 0,
        "axiom_query_count": sum(len(row["axiom_queries"]) for row in results),
        "allowed_axiom_dependencies": sorted(STANDARD_AXIOMS),
        "required_endpoints": sorted(REQUIRED_ENDPOINTS),
        "required_endpoints_audited": endpoints_complete,
        "results": results,
        "all_passed": all_passed,
    }
    return report, all_passed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--timeout", type=float, default=300, metavar="SECONDS",
                        help="maximum compilation time per source file (default: 300)")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    try:
        report, passed = verify(args.timeout)
    except (ManifestError, VerificationError, OSError, UnicodeError) as error:
        report = {"schema_version": 1, "all_passed": False, "error": public_diagnostics(str(error))}
        passed = False
    REPORT.parent.mkdir(parents=True, exist_ok=True)
    temporary = REPORT.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    temporary.replace(REPORT)
    print("Verification passed." if passed else "Verification failed.")
    print("Report: verification/local-report.json")
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
