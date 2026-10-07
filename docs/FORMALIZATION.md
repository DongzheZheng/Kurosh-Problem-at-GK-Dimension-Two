# Formalization

The library works with the free associative algebra on two letters over a field $F$. Homogeneous words form the degree spaces. Compatible dual spaces at dyadic scales define a homogeneous two-sided ideal by testing all word cuts against arbitrary exterior linear functionals. The positive part of its quotient is the initial nil algebra.

The final algebra is the positive part of a further homogeneous quotient. This quotient supplies primeness and graded just infinitude while retaining the nil relations and growth bounds. The construction fixes $Q$ over $F$ before quantifying over field extensions.

## Main declarations

All five declarations below are in the namespace `CriticalGK2.Actual`.

| Declaration | Statement |
| --- | --- |
| `originalField_critical_gk_two_absolute_nil_endpoint` | The initial two-generator construction has GK dimension two and is nil in all matrix sizes after every field extension. |
| `exists_prime_critical_gk_two_absolute_nil` | The final positively graded prime algebra satisfies the prescribed-envelope bound, graded just infinitude, residual finite-dimensionality, and absolute matrix nilpotence. |
| `exists_prime_critical_gk_two_absolute_nil_default` | The existence theorem takes an arbitrary field as its sole mathematical input. |
| `exists_unital_critical_gk_two_absolute_algebraic` | The unitization is two-generated, infinite-dimensional, and of GK dimension two; its scalar extensions are algebraic in all matrix sizes. |
| `exists_same_prime_critical_algebra_and_absolute_unitization` | A single quotient ideal determines $Q$ and its unitization $B$, with all properties in one existence theorem. |

In the prescribed-envelope theorem, the ordinary inputs are the field and a function $\Lambda$ that is nondecreasing, at least one in positive degrees, and tends to infinity. The field-only theorem supplies these conditions internally for $\Lambda(n)=n$.

## Objects and conventions

`PositiveWordIdealQuotient F I hpos` is the augmentation kernel in the free-algebra quotient by the constructed ideal $I$. Its generators are the actual images of the two free letters.

`positiveIdealDegreeSpace F I hpos m` denotes ordinary degree $m+1$. Thus multiplication takes indices $m,n$ to $m+n+1$. The degree filtration is proved equal to the span of nonempty words of bounded length in the same two generators. Its finite dimension is `positiveIdealDegreeGrowth`.

The logarithmic growth ratio is computed from this word filtration. The proof establishes convergence to two and hence the GK-dimension value. The unital word filtration of $B=F\oplus Q$ has dimension $1+\gamma_Q(n)$.

`positivePower M e` denotes the ordinary positive power $M^{e+1}$. The bounded-degree theorem has the quantifier order

$$
\forall r,d\ge1\ \exists N\ \forall K/F\ \forall M\in M_r((Q\otimes_F K)_{\le d}),
\qquad M^{N+1}=0.
$$

`OrdinaryNonUnitalPrime` quantifies over ordinary two-sided ideals. Graded just infinitude quantifies over homogeneous $F$-linear two-sided ideals. Residual finite-dimensionality uses the actual maps to finite-dimensional truncation quotients.

For the unital result, the library constructs the $K$-algebra equivalence

$$
(F\oplus Q)\otimes_F K\cong K\oplus(K\otimes_F Q).
$$

This identifies the unitization theorem with the literal tensor extension appearing in the statement.

## Module guide

| Part of the proof | Principal modules |
| --- | --- |
| Free words, homogeneous spaces, and tensor coordinates | `ActualWordSpaces`, `WordTensor`, `WordTensorSuffix` |
| Dyadic coherence and the homogeneous all-cut ideal | `DyadicCoherence`, `AllCutIdeal`, `HomogeneousProjection`, `PrimalCompletion` |
| Prefix extension and contraction dimensions | `WaitingCutRank`, `ActualWordCutRank`, `ActualStemBudget`, `RootCutSupportBudget` |
| Matrix identities and finite automata | `MatrixPI`, `PISegment`, `SuffixAutomaton`, `AutomatonFiniteEvaluation`, `AutomatonScalarReadback` |
| Infinite construction and matrix nilpotence | `SparseConstruction`, `SparseGlobalCutBudget`, `SparseAbsoluteMatrixNil`, `PositiveWordIdealScalarNil` |
| Growth estimates and normal-word lower bounds | `ActualEnvelopeGrowth`, `ActualGrowthLowerBound`, `NormalWordGreedyBasis`, `NormalWordFactorial`, `FactorComplexity` |
| Prime quotient and graded just infinitude | `HomogeneousIdealZorn`, `InitialDegreeIdeal`, `GenericPositivePrime`, `PositiveWordIdealJustInfinite` |
| Scalar extension and unitization | `UnitizationScalarBaseChange`, `ActualUnitizationGrowthEndpoint`, `UnitalCriticalEndpoint` |

## Implementation choices

The formalization uses a one-hot encoding of PI words, with block length $D_k=(k^2+1)^2$, and an automaton whose states share word prefixes. These choices simplify injectivity and evaluation proofs. The linked manuscript uses a shorter binary encoding and an independent-path presentation of the automaton. The two implementations give the same existence theorem.

The PI block uses the alternating product on $p=k^2+1$ matrix arguments. The standard basis of $M_k(R)$ has $k^2$ elements, so an alternating map on more than $k^2$ arguments vanishes over any commutative coefficient ring $R$. This identity is proved in `MatrixPI.lean` by a basis-and-pigeonhole argument.

The construction establishes arbitrarily close superquadratic growth envelopes and GK dimension two. A quadratic upper bound remains a further question.
