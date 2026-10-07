# The Kurosh Problem at GK Dimension Two: Nil Algebras over Arbitrary Fields

**Infinite-dimensional, two-generated nil algebras of Gelfand–Kirillov dimension two over every field.**

This repository contains a Lean 4 formalization of a solution to the critical-dimension case of the quantitative Kurosh problem. The theorem answers Questions 5 and 6 in Bell–Small–Smoktunowicz's [*Primitive algebraic algebras of polynomially bounded growth*](https://doi.org/10.1090/conm/562/11129): the existence of infinite-dimensional affine algebraic algebras of finite GK dimension over uncountable fields, and the existence of an infinite-dimensional affine algebraic algebra of GK dimension exactly two. Both questions are recorded in the introduction to Greenfeld's [*The Quantitative Kurosh Problem*](https://doi.org/10.1017/fms.2025.1) (2025).

**Paper:** [*The Kurosh Problem at Gelfand–Kirillov Dimension Two: Nil Algebras over Arbitrary Fields*](https://doi.org/10.13140/RG.2.2.14257.34406), Denzel Zheng.

## Main theorem

Let $F$ be any field. There exists a two-generated, infinite-dimensional, positively graded nonunital $F$-algebra $Q$ such that

$$
\operatorname{GKdim} Q=2,
\qquad
M_r(Q\otimes_F K)\ \text{is nil for every }r\ge1\text{ and every field extension }K/F.
$$

The algebra $Q$ can be chosen prime, graded just infinite, and residually finite-dimensional. Given any nondecreasing function $\Lambda:\mathbb N_{\ge1}\to[1,\infty)$ tending to infinity, the construction also gives

$$
\frac{n(n+3)}2\le\gamma_Q(n)\le4(n+1)^2\Lambda(n),
\qquad
\gamma_Q(n)=\sum_{j=1}^{n}\dim_F Q_j.
$$

For each matrix size $r$ and degree bound $d$, a common nilpotence exponent works over all field extensions and for all matrices with entries in degrees at most $d$.

The same $Q$ has a unitization $B=F\oplus Q$ that is two-generated, infinite-dimensional, and of GK dimension two. Every $M_r(B\otimes_F K)$ is algebraic over $K$.

The growth bound permits an arbitrarily slowly diverging factor above quadratic growth. An upper bound $\gamma_Q(n)=O(n^2)$ has not been obtained.

## Background

Kurosh asked in 1941 whether every finitely generated algebraic algebra is finite-dimensional. Golod's 1964 construction, based on the Golod–Shafarevich inequality, produced infinite-dimensional nil algebras of exponential growth. Growth restrictions then became a central part of the problem.

Lenagan–Smoktunowicz obtained polynomially bounded nil algebras over countable fields in 2007; Lenagan–Smoktunowicz–Young reduced the GK-dimension bound to three. Bell–Young developed arbitrary-field constructions with arbitrarily slow superpolynomial growth. Subsequent work by Smoktunowicz–Young, Smoktunowicz–Bartholdi, Alahmadi–Alsulami–Jain–Zelmanov, Greenfeld–Zelmanov, and Greenfeld advanced low-growth radical algebras and the realization of nil-algebra growth.

The Bergman gap theorem, the Small–Stafford–Warfield dimension-one theorem, and Kaplansky's finiteness theorem for affine algebraic PI algebras place the infinite-dimensional algebraic problem at the critical boundary $\operatorname{GKdim}=2$. Shirshov's height theorem gives a combinatorial proof of the PI finiteness result. References and a timeline appear in [Background and references](docs/HISTORY.md).

## Proof architecture

The construction combines dyadic spaces in the two-generator free algebra with an ideal defined by contractions at every word cut. Extending a common prefix tensor preserves the maximal contraction dimension over word cuts. Weighted finite automata and alternating matrix identities impose matrix nilpotence relations, while sparse scheduling controls growth. Normal-word complexity supplies the quadratic lower bound. A maximal homogeneous quotient provides primeness and graded just infinitude.

The formalization uses one-hot word encodings and shared-prefix automata. Its objects, quantifiers, and theorem declarations are described in [Formalization](docs/FORMALIZATION.md).

## Build and verification

The project uses **Lean 4.29.0** and mathlib commit `8a178386ffc0f5fef0b77738bb5449d50efeea95`. Install [elan](https://github.com/leanprover/elan), then run from the repository root:

```sh
lake update
lake exe cache get
lake build
```

For a fresh module-by-module check with source hashes and axiom-dependency queries:

```sh
python3 scripts/check_manifest.py
lake env python3 scripts/verify.py
```

The main declarations are listed in [Verification.lean](Verification.lean). Their foundational dependencies are `propext`, `Classical.choice`, and `Quot.sound`. The verification script records compiler results, source hashes, and these dependencies in `verification/local-report.json`.

See [Reproducing the verification](docs/VERIFICATION.md) for the release record and checks.

## Entry points

| Result | Source |
| --- | --- |
| Main theorem with a prescribed growth envelope | [PrimeCriticalEndpoint.lean](CriticalGK2/PrimeCriticalEndpoint.lean) |
| Existence over an arbitrary field | [PrimeCriticalDefault.lean](CriticalGK2/PrimeCriticalDefault.lean) |
| Algebraic unitization and scalar extension | [UnitalCriticalEndpoint.lean](CriticalGK2/UnitalCriticalEndpoint.lean) |
| Joint theorem for the same $Q$ and $B$ | [PaperCriticalEndpoint.lean](CriticalGK2/PaperCriticalEndpoint.lean) |
| Library import | [CriticalGK2.lean](CriticalGK2.lean) |

## Citation

Please cite the [paper](https://doi.org/10.13140/RG.2.2.14257.34406) when using the construction or its results. Repository citation metadata is provided in [CITATION.cff](CITATION.cff).

**Keywords:** Kurosh problem; quantitative Kurosh problem; Gelfand–Kirillov dimension; affine algebraic algebras; nil algebras; polynomial growth; uncountable fields; absolutely stably nil; matrix algebras; scalar extension; Jacobson radical; graded just infinite; residual finite-dimensionality; tensor contractions; word complexity; matrix polynomial identities; Shirshov height theorem; Lean 4; mathlib.
