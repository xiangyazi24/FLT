# Q180 (dm1): stress test of the `ωₙ` / projective bridge plan

## Executive audit

The plan is mathematically sound **if** the projective formula is proved as a universal polynomial identity / homogeneous coordinate formula, not by counting torsion roots or by invoking separability.  The two serious seams are:

```text
A/B: define ωₙ as an actual polynomial and prove the projective formula
C: prove φₙ(P) ≠ 0 at ψₙ(P)=0 without using separability
```

The local-parameter computation after `ωₙ` exists is comparatively small.  The largest risk is **not** dual-number algebra; it is making `ωₙ` into a polynomial with the right normalization and proving the `[n]P = [φₙ:ωₙ:ψₙ]` formula non-circularly.

A realistic size estimate for a robust general-`n` version is closer to **1000+ lines**, not 200–400.  A characteristic-zero prototype using quotient/division by `2` could be significantly smaller, perhaps **400–700 lines**, but the final arbitrary-characteristic statement `(n : K) ≠ 0` needs an integral/universal construction or an equivalent recurrence definition.

---

## (1) Circularity check for the projective formula

### Does the projective formula require separability?

No, not inherently.  The formula

```text
[n]P = [φₙ(P) : ωₙ(P) : ψₙ(P)]
```

is a formula for the multiplication-by-`n` morphism.  It is not a statement about the kernel being reduced, and it does not require that the roots of `ψₙ` are simple.  It can be proved by induction from the group law / addition formulas and polynomial identities.

However, there are two ways to prove it, one safe and one dangerous.

### Safe proof style

Prove it as a homogeneous polynomial identity / coordinate formula, preferably over a universal ring or over an arbitrary commutative ring where the raw Jacobian formulas make sense:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula
import Mathlib.Tactic

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

noncomputable section

variable {R : Type*} [CommRing R]
variable (W : WeierstrassCurve R)

/-- Schematic target: the projective division-polynomial representative. -/
def divPolyJacobianRep (n : ℤ) : Fin 3 → R[X][Y] :=
  ![W.φ n, W.ω n, W.ψ n]

/-- Schematic non-circular theorem: this is a polynomial-coordinate identity,
not a statement about the reduced kernel. -/
theorem jacobian_formula_divPolyRep
    (n : ℤ) :
    -- `divPolyJacobianRep W n` agrees with the recursively defined raw Jacobian
    -- multiplication formula modulo the Weierstrass equation / coordinate ring.
    True := by
  sorry

end

end WeierstrassCurve
```

This proof can use:

```lean
Jacobian.dblXYZ
Jacobian.addXYZ
Jacobian.map_dblXYZ
Jacobian.map_addXYZ
```

because the raw formulas are over `CommRing` representatives.  It should not use root-counting, torsion cardinality, separability, or `[n]` being étale.

### Dangerous / circular proof style

Avoid proving the formula by arguing:

```text
both sides agree on all points / all n-torsion points / enough roots
```

because “enough roots” or “all torsion points are reduced” is exactly the separability/torsion theorem we are trying to prove.  Similarly, avoid proving nonzero denominators using separability of `ψₙ`.

### Does the group law itself require separability?

The ordinary group law on a smooth Weierstrass curve over a field does not require `[n]` to be étale.  It is available independently of separability.  But for dual numbers, Mathlib does not package the group law as a point group over `TrivSqZeroExt K K`; only the raw Jacobian coordinate polynomials are ring-level.  So the non-circular Lean path is to prove the coordinate formula with raw polynomials, not by using a pre-existing dual-number group.

---

## (2) The coprimality seam `φₙ(P) ≠ 0` at `ψₙ(P)=0`

### Does `mk_φ` help?

Yes, but only partially.  It gives the identity in the coordinate ring / at a point:

```text
φₙ = x * ψₙ² - ψₙ₊₁ ψₙ₋₁
```

or, in the reduced univariate version,

```text
Φₙ = X * ΨSqₙ - preΨₙ₊₁ * preΨₙ₋₁ * parity_factor.
```

At a non-2-torsion point where `ψ₂(P)` is a unit, `ψₙ(P)=0` is equivalent to `preΨ'_n(x)=0`.  Then the `x * ψₙ²` term vanishes, so

```text
φₙ(P) = - ψₙ₊₁(P) * ψₙ₋₁(P)
```

up to the known reduced/full `ψ₂` unit factors.  Therefore `φₙ(P) ≠ 0` follows from adjacent nonvanishing:

```text
ψₙ(P)=0  ⇒  ψₙ₋₁(P) ≠ 0 ∧ ψₙ₊₁(P) ≠ 0.
```

### Is adjacent nonvanishing in Mathlib?

Not as a standard Mathlib theorem in the division-polynomial API.  Mathlib has the EDS definitions/recurrences and coordinate-ring identities, but not the full rank-of-apparition theorem for evaluated division polynomials.

In the FLT scratch work, this is exactly the kind of lemma you have been building under the Keystone/Coprimality umbrella:

```lean
-- schematic names
no_adjacent_preΨ_zero
preΨ_eval_zero_iff_rank_dvd
preΨ_eval_zero_iff_three_dvd_of_Ψ₃_eval_zero
Ψ₂Sq_eval_ne_of_Ψ₃_eval_zero
preΨ₄_eval_ne_of_Ψ₃_eval_zero
```

If those are available non-circularly, then use them here.  If not, item C is a real additional seam.

### Is this the same as bridge-1 `preΨ'_root_Ψ₂Sq_ne`?

No.  They are related but not the same.

Bridge-1 says:

```lean
(W.preΨ' n).IsRoot x → W.Ψ₂Sq.eval x ≠ 0
```

It excludes 2-torsion roots of the reduced division polynomial.

Item C needs:

```lean
(W.preΨ' n).eval x = 0 →
  (W.preΨ' (n-1)).eval x ≠ 0 ∧ (W.preΨ' (n+1)).eval x ≠ 0
```

or the corresponding integer-indexed `preΨ` statement.  This is the “no adjacent vanishing” / rank-of-apparition theorem.  It uses some of the same small resultant base facts, but it is strictly stronger/different.

### Lean target for C

```lean
namespace WeierstrassCurve

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- Non-circular adjacent nonvanishing, the real input behind `φₙ(P) ≠ 0`. -/
theorem preΨ'_adjacent_ne_of_root
    {n : ℕ} {x : K}
    (hn : n ≠ 0) -- plus whatever side conditions your integer-indexed theorem needs
    (hroot : (W.preΨ' n).eval x = 0)
    (h2 : W.Ψ₂Sq.eval x ≠ 0) :
    (W.preΨ' (n + 1)).eval x ≠ 0 ∧
      (if hn1 : 1 ≤ n then (W.preΨ' (n - 1)).eval x ≠ 0 else True) := by
  -- Derived from integer-indexed no-adjacent-zero theorem for `preΨ`.
  sorry

/-- `φₙ(P)` nonzero at a non-2-torsion `ψₙ`-root. -/
theorem phi_ne_zero_of_psi_eq_zero_non_two
    {n : ℕ} {x y : K}
    (hP : W.Equation x y)
    (hpsi : /* ψₙ(P)=0 */ True)
    (h2 : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (hadj : /* adjacent nonvanishing */ True) :
    /* φₙ(P) ≠ 0 */ True := by
  -- Use `mk_φ` / `Φ` identity; after `ψₙ=0`, reduce to product of adjacent ψ's.
  sorry

end WeierstrassCurve
```

If item C is not already established, it may be as large as the `ωₙ` bridge for general `n`.

---

## (3) Definition of `ωₙ` as an actual polynomial

### The identity is a specification, not a definition

The identity

```text
2 * ψₙ * ωₙ = ψ₂ₙ - ψₙ² * (a₁ φₙ + a₃ ψₙ²)
```

is the correct normalization, but it does not define `ωₙ` until you prove the right-hand side is divisible by `2 * ψₙ` in the polynomial ring.

At a point with `ψₙ=0`, this identity reduces to `0=0`, so it does not determine the value of `ωₙ(P)`.  For the local-parameter bridge you need `ωₙ` as a polynomial with a value at `P`, not only the defining identity after multiplication by `ψₙ`.

### Is the alternative formula better?

The common formula

```text
ωₙ = (ψₙ₊₂ ψₙ₋₁² - ψₙ₋₂ ψₙ₊₁²) / (4 ψₙ)
```

is not a magic escape hatch.

For short Weierstrass equations (`a₁=a₃=0`) it is closely related to the standard `ωₙ`, because

```text
ψ₂ₙ = (ψₙ / ψ₂) * (ψₙ₊₂ ψₙ₋₁² - ψₙ₋₂ ψₙ₊₁²)
```

and `ψ₂ = 2y`.  But in the general Weierstrass normalization, the Mathlib-compatible formula is the documentation formula involving

```text
ψ₂ₙ / ψₙ - ψₙ * (a₁ φₙ + a₃ ψₙ²).
```

The proposed formula still requires division by `ψₙ` and by `4`, and it is not the clean final definition in characteristic `2` or for general `a₁,a₃`.  It is useful as a derived identity, not as the main definition.

### Practical definition options

#### Option A: characteristic-zero / `2` invertible prototype

If your immediate application is characteristic zero, define a prototype by polynomial quotient:

```lean
noncomputable def omegaDivPoly_charZero
    {K : Type*} [Field K] (W : WeierstrassCurve K) (n : ℤ) : K[X][Y] :=
  ((W.ψ (2*n)) / (W.ψ n)
    - W.ψ n * (C (C W.a₁) * W.φ n + C (C W.a₃) * W.ψ n ^ 2)) / 2
```

Then prove:

```lean
theorem two_mul_ψ_mul_omegaDivPoly_charZero
    (hψdvd : W.ψ n ∣ W.ψ (2*n)) :
    (2 : K[X][Y]) * W.ψ n * W.omegaDivPoly_charZero n =
      W.ψ (2*n)
        - W.ψ n ^ 2 * (C (C W.a₁) * W.φ n + C (C W.a₃) * W.ψ n ^ 2) := by
  -- Requires `2 ≠ 0`, and quotient cancellation via `hψdvd`.
  sorry
```

This is the fastest way to validate the bridge in characteristic zero, but it is not final for arbitrary `(n : K) ≠ 0`.

#### Option B: use EDS complement to avoid quotient by `ψₙ`

Mathlib’s EDS file already has complement sequences:

```lean
complEDS₂
complEDS'
complEDS
normEDS_mul_complEDS₂
normEDS_dvd_normEDS_two_mul
```

These witness divisibility in the abstract EDS:

```text
W(k) ∣ W(n*k).
```

This suggests a better internal definition for the quotient `ψ₂ₙ / ψₙ`:

```text
ψ₂ₙ / ψₙ  :=  complement sequence at k=n, multiplier=2.
```

For the bivariate `ψ`, the quotient for `2n` should be expressible through the existing `complEDS₂`/`complEDS` machinery after matching `ψ` with `normEDS`.  Then define

```text
2ωₙ = quotient₂ₙ - ψₙ * (a₁ φₙ + a₃ ψₙ²).
```

You still need divisibility by `2` integrally if you want all characteristics.  But this is closer to Mathlib’s design than raw polynomial division.

Schematic Lean shape:

```lean
namespace WeierstrassCurve

open Polynomial
open scoped Polynomial.Bivariate

variable {R : Type*} [CommRing R]
variable (W : WeierstrassCurve R)

/-- Quotient polynomial representing `ψ₂ₙ / ψₙ`.  Ideally defined via EDS complement. -/
noncomputable def psiTwoMulQuot (n : ℤ) : R[X][Y] := by
  -- Use `complEDS₂` / `complEDS` after identifying `W.ψ` with `normEDS`.
  exact 0

/-- Final bivariate `ωₙ`.  For an integral version, this should be constructed so that
`two_mul_omega` is a theorem, not by division in `R`. -/
noncomputable def omegaDivPoly (n : ℤ) : R[X][Y] := by
  -- Universal/integral construction or a recurrence.
  exact 0

end WeierstrassCurve
```

#### Option C: recurrence definition for `ωₙ`

You can define `ωₙ` by a recurrence coupled to `ψₙ` and `φₙ`, but this is likely to be awkward.  The recurrence for the `y`-coordinate numerator is not as simple as the EDS recurrence for `ψₙ`, and proving it matches the projective formula will still require the same addition-formula algebra.

I would not choose recurrence-first unless the quotient/divisibility route becomes blocked.

### Recommendation for `ωₙ`

For speed:

```text
char-zero prototype: quotient definition
```

For final Mathlib-quality theorem:

```text
EDS-complement quotient for ψ₂ₙ/ψₙ + universal/integral proof of divisibility by 2
```

The alternative `(ψ_{n+2}...)/(4ψ_n)` should be a lemma, not the primary definition.

---

## (4) Size estimate

A realistic estimate depends on whether you prototype in characteristic zero or build the final integral object immediately.

### Characteristic-zero prototype

```text
A. omega definition by quotient/division by 2          80–150 lines
B. projective formula, evaluated/char-zero version    250–450 lines
C. φ nonzero from no-adjacent theorem                  80–200 lines if no-adjacent already exists
D. ω nonzero from equation at Z=0                      30–80 lines
E. local parameter over dual numbers                   80–150 lines
F. connect to TangentO/separability                    80–150 lines
---------------------------------------------------------------
Total                                                 600–1200 lines
```

If C is fully available and B is restricted to the exact evaluated theorem needed for the bridge, this could land near the lower end.

### Final arbitrary-characteristic theorem

```text
A. integral omega / divisibility by 2                  250–600 lines
B. projective formula over CommRing/universal ring     400–900 lines
C. non-circular φ/ψ no-common-root                     200–600 lines if not already complete
D-F local bridge and assembly                          200–400 lines
---------------------------------------------------------------
Total                                                1000–2500+ lines
```

So this is not a 200-line project.  A 200–400 line result is plausible only if:

1. `ωₙ` is defined by quotient in a field with `2 ≠ 0`,
2. the projective formula is weakened to the exact local evaluated statement,
3. the no-adjacent/no-common-root theorem is already available,
4. you do not attempt a Mathlib-quality integral definition.

---

## (5) Single most likely failure point

The most likely failure point is:

```text
Defining ωₙ as a genuine polynomial with the right normalization and proving the
projective formula [n]P = [φₙ:ωₙ:ψₙ] without importing separability/torsion facts.
```

More specifically, the problem will probably appear as one of these:

```text
• quotient/divisibility: proving ψₙ ∣ ψ₂ₙ and divisibility by 2 in the right ring;
• normalization mismatch: Mathlib's ψ/φ/preΨ conventions differ by ψ₂ or powers/signs;
• projective formula: the induction needs exactly the right weighted Jacobian coordinates;
• characteristic 2: division by 2 prototype does not generalize to `(n : K) ≠ 0`.
```

The second most likely failure point is C:

```text
φₙ(P)≠0 at ψₙ(P)=0
```

if the no-adjacent/rank-of-apparition theorem is not fully established non-circularly.  This seam is logically independent of `ωₙ`: even with a perfect `ωₙ`, the local parameter formula needs `ωₙ(P)` to be a unit/nonzero, and that goes through `φₙ(P)≠0` or an equivalent no-zero-coordinate theorem.

---

## Recommended refinement before coding

Split the work into three named seams and keep them independent:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.Tactic

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- Seam A/B: missing bivariate projective Y-coordinate division polynomial. -/
noncomputable def omegaDivPoly (n : ℤ) : K[X][Y] := by
  -- First prototype may use quotient; final version should be integral.
  exact 0

/-- Seam A: normalization identity for `ωₙ`. -/
theorem two_mul_psi_mul_omegaDivPoly (n : ℤ) :
    (2 : K[X][Y]) * W.ψ n * W.omegaDivPoly n =
      W.ψ (2*n)
        - W.ψ n ^ 2 * (C (C W.a₁) * W.φ n + C (C W.a₃) * W.ψ n ^ 2) := by
  sorry

/-- Seam B: projective formula, stated in the exact evaluated form needed later. -/
theorem jacobian_nsmul_eval_eq_phi_omega_psi
    (n : ℤ) {x y : K}
    (hP : W.Equation x y) :
    -- `[n]![x,y,1]` is represented by
    -- `![φₙ(x,y), ωₙ(x,y), ψₙ(x,y)]`.
    True := by
  sorry

/-- Seam C: nonzero target Y-coordinate at a torsion root. -/
theorem omegaDivPoly_eval_ne_zero_of_psi_eval_zero
    (n : ℤ) {x y : K}
    (hP : W.Equation x y)
    (hpsi : /* W.ψ n evaluated at (x,y) = 0 */ True)
    (hphi : /* W.φ n evaluated at (x,y) ≠ 0 */ True) :
    /* W.omegaDivPoly n evaluated at (x,y) ≠ 0 */ True := by
  -- Use the projective Weierstrass equation at Z=0:
  -- `ω² = φ³` up to the Mathlib Jacobian convention.
  sorry

/-- Seam E: local parameter formula from projective coordinates. -/
theorem localParameter_nsmul_dual_eq_neg_phi_mul_psi_div_omega
    (n : ℤ) {x y : K}
    (hP : W.Equation x y)
    (homega : /* omega eval is nonzero */ True) :
    -- `t([n]Pε) = -φₙ(Pε)*ψₙ(Pε)/ωₙ(Pε)`.
    True := by
  sorry

end

end WeierstrassCurve
```

This split keeps circularity visible:

* Seam A/B must be polynomial/projective formula only.
* Seam C must use no-adjacent/rank-of-apparition, not separability.
* Seam E is local algebra over dual numbers.
* Seam F should only assemble these with `TangentO.nsmul₁_eq_natCast_mul`.

## Final verdict

The plan survives the stress test, but the original 200–400 line estimate is too optimistic for a final general theorem.  The projective formula itself is non-circular if treated as a polynomial identity.  `mk_φ` helps item C, but it does not solve it; you still need no-adjacent nonvanishing.  The defining identity for `ωₙ` is not enough to define `ωₙ`; you need a quotient/divisibility construction or a recurrence/universal construction.  The single highest-risk item is the `ωₙ` polynomial plus projective formula normalization.
