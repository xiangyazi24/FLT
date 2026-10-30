# NEW 2026-10-30 — N25 arithmetic route review

Status: **NEW paper/source review, conditional route, NOT a recovered October 7 manuscript; NOT a complete Lean proof.** No Lean build, Magma/Sage job, platform mission, production-source mutation, or remote write was performed for this addendum. The only new executable arithmetic check is the 15-point F2 enumeration attached below. The request's two F2 theorems are accepted as supplied proved inputs; source inspection is not a fresh compilation.

Request: FLT-N25-ROUTE-DELIVER-20261030 r1, commit 70dd1fedf442be02700eb644df531abe28de98f6. Source pin: ec88cc6179136943cd82916b6f2e911aa4a07a25. All four required SHA256 values match the input manifest; see SOURCE-HASHES.txt. This is restricted to RNOTE-N25-ROUTE r1, not a campaign restart.

## 1. Useful conclusion first

There is a clean **conditional** reduction proof of the five-cusp assertion which avoids a fresh F3 Picard count and even avoids determining the order of the rational Jacobian. At 2, one must NOT assume reduction injects on all torsion. Instead its torsion kernel is killed by 2; nonhyperellipticity then rules out two distinct rational curve points in one residue disk. The hard remaining arithmetic input is torsion of the relevant rational point differences (finiteness of J(Q) suffices). Primary literature supplies rank zero for the genus-12 J1(25), but applying it to this genus-4 model still requires the actual modular-curve morphism and a Jacobian pullback/norm bridge. The four pinned files and the additional inspected definitions do not themselves supply that bridge.

## 2. What the pinned definitions actually say

Write C for the projective zero locus of

    -xz - xw + y² + yz + zw = 0,
    x²w + xyz - xyw - xzw + yzw + z²w - zw² = 0.

`RationalPointsN25CanonicalPoints.lean` defines these rational-coordinate equations, `NonzeroQuadruple`, projective equality, and `IsCanonicalCusp25`. Its five cusp representatives are (0:0:0:1), (0:-1:1:0), (1:1:0:1), (0:0:1:0), (1:0:0:0). `canonical_point_with_zero_coordinate_is_cusp` (line 386) proves the boundary assertion; it does not classify the dense open subset. `noncuspidal_point_to_plane_sextic` is a birational reduction, not a descent obstruction.

`N25F_ClassNumberUpper.Pic25 n` is the degree-n fiber of the **F2** full divisor-class quotient. `N25F_FullPicardDegree` makes its principal subgroup the range of the actual function-field principal-divisor map. `N25F_ClassNumberLower.card_picDegreeZero_eq_seventy_one` proves `Fintype.card (Pic25 0) = 71`; its explicit order-71 class lives on that special fiber. It is not a theorem that J(Q) has order 71, is finite, or has rank zero, nor is its special-fiber principal-function certificate automatically a characteristic-zero identity.

`N25F_AbelJacobi.pointDiffClass_ne_zero` separates closed-point classes when the pole point has degree at most two. It is not the statement that doubled generic-fiber rational-point classes are distinct. The stronger special-fiber `N25F_ClassNumberUpper.effClass_two_injective` concerns effective degree-two divisors, still over F2. A specialization/gonality bridge remains necessary if that theorem is used to prove the corresponding generic-fiber property.

Source links (all immutable):
- https://github.com/xiangyazi24/FLT/blob/ec88cc6179136943cd82916b6f2e911aa4a07a25/FLT/Assumptions/MazurProof/RationalPointsN25CanonicalPoints.lean
- https://github.com/xiangyazi24/FLT/blob/ec88cc6179136943cd82916b6f2e911aa4a07a25/FLT/Assumptions/MazurProof/N25F_ClassNumberUpper.lean
- https://github.com/xiangyazi24/FLT/blob/ec88cc6179136943cd82916b6f2e911aa4a07a25/FLT/Assumptions/MazurProof/N25F_ClassNumberLower.lean
- https://github.com/xiangyazi24/FLT/blob/ec88cc6179136943cd82916b6f2e911aa4a07a25/FLT/Assumptions/MazurProof/N25F_FullPicardDegree.lean
- https://github.com/xiangyazi24/FLT/blob/ec88cc6179136943cd82916b6f2e911aa4a07a25/FLT/Assumptions/MazurProof/N25F_AbelJacobi.lean

## 3. Precise conditional theorem and proof

Assume:

G1. The displayed projective (2,3) zero locus over Z2 is a smooth proper geometrically connected curve model. Its generic fiber is identified with the rational-coordinate curve C, and its special fiber is identified both with the raw mod-2 zero locus of the displayed equations and with the curve represented by the existing F2 divisor/function-field infrastructure. These identifications commute with normalized projective-coordinate reduction. In particular the 15-quadruple check below enumerates points of this actual special fiber, not merely points of an unrelated reduction of generic equations.

G2. The generic fiber is geometrically nonhyperelliptic of genus 4. A genuine smooth canonical complete intersection of type (2,3) in P3 provides this; simply writing two equations or calling the model canonical does not provide a certificate.

G3. The relative Jacobian is an abelian scheme over Z2, and its Abel–Jacobi map with a rational cusp basepoint is compatible with reduction and the existing special-fiber class map.

A. J(Q) is torsion (finiteness is sufficient). In fact it suffices that [P-Q] is torsion whenever P is rational and Q is the cusp with the same reduction.

Then C(Q) consists of the five displayed cusp classes.

Proof. Normalize any rational projective point over Z2. Properness gives reduction in C(F2). Enumeration of the 15 nonzero binary quadruples gives precisely the five cusp reductions, all distinct (attached executable check). Choose the cusp Q with the reduction of P. Then D=[P-Q] belongs to the reduction kernel of J(Q2), and A makes D torsion. The formal-kernel lemma below gives 2D=0. If P differs from Q, the divisor 2P-2Q is nonzero and principal over the algebraic closure, giving a degree-two map C to P1, contradicting G2. Thus P=Q in projective space. The five representatives satisfy the equations over Q, proving the reverse inclusion. No rational-function descent is needed: the contradiction already occurs over the algebraic closure.

This is a complete argument *from G1–G3 and A*. It is not an assertion that those hypotheses have been discharged in the pinned Lean project. In particular the target axiom has not been removed.

### Elementary formal-kernel lemma (NEW paper derivation)

For an integral commutative g-dimensional formal group F over Z2, use its usual parameters on the kernel of reduction. The multiplication series satisfies [a](T)=aT+terms of total degree at least two, with integral coefficients. Consequently [2] sends (2Z2)^g into (4Z2)^g.

The group F((4Z2)^g) is torsion-free: if x is nonzero and n=min_i v2(x_i)≥2, then the minimum valuation of [2]x is exactly n+1. Indeed its linear term has minimum n+1 while every nonlinear term has valuation at least 2n>n+1. Multiplication by an odd integer preserves minimum valuation n by the same argument. Iterating proves that no nonzero integer can annihilate x. Convergent integral power series justify the valuation estimates. Thus if x in F((2Z2)^g) is torsion, [2]x is torsion in the torsion-free deep subgroup, so [2]x=0.

This proves only exponent ≤2 for torsion in the reduction kernel, NOT its triviality. It works in dimension four with mixed quadratic terms; it is not an elliptic-curve-only assertion. Formal completion identifying the abelian-scheme reduction kernel with these parameters is part of G3, not established by this short power-series argument.

## 4. Arithmetic source and exact outstanding transfer

Derickx–van Hoeij, *Gonality of the modular curve X1(N)*, Journal of Algebra 417 (2014), 52–71, author version arXiv:1307.5719v3, §5 Lemma 1(3), pp12–13, proves finiteness for J1(25)(Q). The argument uses certified nonvanishing L-values and Kato, not Mazur's torsion classification. The same discussion explicitly gives #J1(25)(F3)=2,503,105, an odd number. These are **literature results for genus 12**, not computations run here and not a count for our genus-4 Jacobian.
https://arxiv.org/pdf/1307.5719v3
https://doi.org/10.1016/j.jalgebra.2014.06.026

A later reference is Derickx–Etropolski–van Hoeij–Morrow–Zureick-Brown, *Sporadic Cubic Torsion*, arXiv:2007.13929v2, Theorem 3.1(2) and Remark 3.2, pp6–7. Its unconditional rank-zero list includes 25; the converse is the part stated conditionally on BSD. It describes exact L-value testing on simple factors and Kato's implication. We use only the forward rank-zero result, not the paper's torsion classification and not an assumed BSD converse.
https://arxiv.org/pdf/2007.13929v2

To transfer finiteness, provide a genuine nonconstant Q-morphism f:X1(25)→C of degree d>0 (or an independently certified Jacobian factor identification). Then f_* f^*=[d] on J(C). Since J1(25)(Q) is finite, the image of f^* on J(C)(Q) is finite, while its kernel is contained in J(C)[d], which is finite in characteristic zero. Hence J(C)(Q) is finite. This is a NEW deduction from the cited genus-12 result and the missing map/norm hypotheses. A map from hypothetical order-25 obstructions to C-points is NOT by itself the required global morphism of smooth projective curves.

LMFDB label 25.150.4.f.1 is a model identifier, not a rank certificate. Direct retrieval of its page failed in this review; no unseen database assertion is used. No explicit degree or formula for f is claimed checked here.

## 5. Which extra arithmetic can be avoided?

| Proposed input | Verdict / cheaper replacement |
|---|---|
| Full numerical rank and full J(Q) structure | Unnecessary for the final disk argument. Torsion of the indicated point differences suffices. Finiteness from the cited modular rank-zero theorem is a sufficient but heavyweight way to obtain it. |
| Rank zero inferred from Pic25 order71 | Invalid: reduction has a large characteristic-zero kernel. Special-fiber cardinality alone gives no rank bound. |
| Injectivity of reduction on all J(Q)_tors at2 | Do not assume it. Replace with the proved-above exponent2 kernel lemma plus generic degree-two gonality. |
| Fresh #Pic0(C/F3) | Not needed for the preferred exponent2 route. An alternative is odd-order torsion, proved via good reduction at an odd prime with odd Jacobian order. That alternative needs an actual F3 count/bridge; no genus-4 number is asserted here. |
| Copy 2,503,105 to the genus-4 model | Invalid. It is J1(25)'s count. Transferring oddness via an isogeny factor would require good models and a Frobenius-factor argument. Finite rational-point groups do not simply surject under every isogeny. |
| Pic25 order71 / special-fiber AJ injectivity | Sound existing data, useful for an explicit class-based route, but logically redundant in the preferred disk-exponent2 proof once the five F2 points are known. The argument does not force these facts into a role they do not have. |
| Descent replacing Kato/rank theory | Possible in principle but not delivered: an explicit finite descent proving all relevant point differences torsion, or directly proving the dense-open sextic has no rational points, would suffice. Merely having a finite Selmer upper bound without rank/saturation conclusion is not enough; no such certificate is claimed. |
| Mazur's no-order25 theorem | Forbidden circular shortcut for this leaf. Not used. |

## 6. Lean statement map and qualitative size estimate

Names below beginning `needed_` are specification labels, NOT claimed existing declarations. Estimates are risk bands, not measured code counts or completion promises; no library-wide absence claim is made from this limited source audit.

1. `needed_model_Z2`: construct smooth proper geometrically connected integral model and identify the two coordinate fibers. Existing input: `canonicalQuadric25`, `canonicalCubic25` and the F2 chart/closed-point infrastructure. **Large**, potentially thousands of lines of model/specialization infrastructure; geometric smoothness is not a 15-rational-point check.
2. `needed_cusps_cover_special_points`: connect normalized rational coordinates/reduction with the five existing `IsCanonicalCusp25` representatives. Raw finite check is tiny; typed adapters **small/medium** (tens to hundreds of lines given model interfaces).
3. `needed_relative_picard_specialization`: rational/generic Picard or Jacobian, reduction homomorphism, and compatibility with `Pic25 0`/`pointDiffClass`. **Very large** if not already reusable: a new characteristic-zero/relative provider, not a finite-field cardinality rewrite.
4. `needed_torsion_kernel_two`: reduction-kernel formal parameters, multiplication-series linear term, valuation convergence, and exponent2 conclusion. Abstract valuation lemma **medium** once formal-group APIs exist; the abelian-scheme interface **large**. The algebraic proof above avoids importing a full formal logarithm implementation.
5. `needed_two_point_divisor_injective_generic`: `2[P]-2[Q]` principal implies projective equality for generic points. **Medium/large** from canonical embedding/nonhyperellipticity, or via a rigorous good-reduction/gonality theorem using existing special effective-degree-two injectivity. `pointDiffClass_ne_zero` cannot be substituted by changing the field in its type.
6. `needed_JQ_torsion`: either formalize the modular source theorem and exact rank certificates plus f/pullback/norm, or supply a new explicit descent. **Dominant/very large**: potentially many-thousand-line or library-scale dependencies if starting from scratch. A cited theorem in this Markdown is not an acceptable replacement Lean axiom.
7. `needed_all_canonical_points_cuspidal`: for x,y,z,w:Q, `NonzeroQuadruple` and the two zero equations imply `IsCanonicalCusp25`. **Small** final glue given items1–6 (roughly tens to low hundreds of lines).
8. Feed that proposition into the existing order25 front end, then eliminate `CyclicExclusion25.no_explicit_order25_obstruction`. **Small expected glue**, but its exact reduction bridge has not been reaudited here and must be checked before claiming closure. The pinned axiom is still present.

## 7. Feasibility judgement

The classical arithmetic route is plausible and sharply delimited: certify the modular quotient/model bridge, use the independently published rank-zero result through pullback/norm, and finish using good reduction plus the exponent2/nonhyperelliptic disk argument. This removes a distracting F3 computation and avoids a false all-torsion injection claim at2. It does not make the Lean task a short patch: relative Jacobian specialization and the noncircular rank-zero provider are the dominant missing dependencies. Therefore order25 is within mathematical reach but not shown here to be within a small fixed formalization budget; a narrowly certified explicit descent might be cheaper, but no completed descent exists in this delivery. Status remains **conditional paper route, source-audited, uncompiled; no complete proof claimed**.
