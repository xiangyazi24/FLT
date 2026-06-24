# Q174 (dm1): minimal Weierstrass formal-group architecture — brainstorm round 1

## Executive assessment

The shortest path is **not** to build the full Silverman formal group law first.  The shortest path is to build the **first-order formal group bridge** that the proof actually needs:

```text
infinitesimal deformation near O  ↔  tangent scalar v ∈ K,
addition near O is v₁ + v₂ to first order,
[n] near O is v ↦ (n : K) * v.
```

You already proved the abstract theorem

```lean
formalNsmul_coeff_one F n = (n : R)
```

for a `FormalGroup`.  That theorem is mathematically perfect, but to use it for `W` you still need to identify the `FormalGroup` with the actual first-order behavior of the Weierstrass curve.  Constructing a full

```lean
W.formalGroup : FormalGroup K
```

is one way to do this, but it is more infrastructure than the separability proof needs.  A smaller interface, something like

```lean
W.formalJetAtO
```

or

```lean
W.tangentAddAtO
```

is likely much faster: prove only the dual-number/degree-1 truncation of the formal group law, then prove `[n]` acts by `(n : K)` on that tangent line by ordinary induction.

My route ranking for the general-`n` separability brick is:

```text
1. First-order formal jet at O + projective/division-polynomial bridge     best Lean path
2. Full Weierstrass formal group law instance                             mathematically clean but heavier
3. Invariant differential / formal logarithm                              elegant but needs differential-form infrastructure
4. Direct derivative of x([n]P)=φ/ψ²                                      likely circular / wrong chart at O
5. Pure EDS recurrence proof of derivative nonvanishing                   possible in principle but disguises formal group
```

The **critical missing piece** is not `formalNsmul_coeff_one`; you already have the abstract version.  The critical missing piece is the bridge:

```lean
preΨ'_n(x + ε dx) = 0 for a dual point Pε
  ⇒ [n](Pε) is an infinitesimal point at O,
```

in a setting where Mathlib’s packaged group law is field-only.  This bridge requires either homogeneous/projective division-polynomial formulas over `TrivSqZeroExt K K`, or a minimal functor-of-points group law over square-zero rings.

---

## (a) Minimal construction of the Weierstrass formal group law

### Full Silverman construction

The standard construction is:

```text
t = -x/y,  w = -1/y,
x = t/w,  y = -1/w,
w = t³ + a₁*t*w + a₂*t²*w + a₃*w² + a₄*t*w² + a₆*w³.
```

Then one solves recursively for `w(t) ∈ R⟦t⟧`, obtains Laurent expansions `x(t), y(t)`, and defines

```text
F(t₁,t₂) = t(P(t₁) + P(t₂)).
```

This gives a genuine one-dimensional commutative formal group law.  It is the right textbook object, but in Lean it requires substantial infrastructure:

* recursive construction of `w(t)` as a formal power series;
* Laurent-series or “power series with pole” bookkeeping for `x(t)` and `y(t)`;
* an addition formula valid over the relevant coefficient ring;
* proof of the formal group axioms, probably by comparison with the group law or by universal polynomial identities.

If your current `FormalGroup` structure requires full associativity/unit/inverse axioms as power-series equalities, then `W.formalGroup : FormalGroup K` by the textbook route is a sizeable project.  It is a good long-term file, but it is not the minimal separability route.

### Minimal first-order construction

For separability, all higher terms of `F` are irrelevant.  Over dual numbers, every term of total degree at least two vanishes.  So the only facts needed are:

```text
F(T₁,T₂) ≡ T₁ + T₂       mod (degree ≥ 2),
[-1](T) ≡ -T              mod (degree ≥ 2),
[n](T) ≡ n*T              mod (degree ≥ 2).
```

This suggests a smaller API:

```lean
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

open Polynomial

namespace WeierstrassCurve

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]

/-- A first-order point at the origin of a Weierstrass curve, represented by its
formal parameter coefficient.  This is intentionally just the tangent line. -/
abbrev FormalJetAtO (W : WeierstrassCurve K) : Type _ := K

/-- Addition of first-order jets at `O`. -/
def FormalJetAtO.add (W : WeierstrassCurve K) :
    FormalJetAtO W → FormalJetAtO W → FormalJetAtO W :=
  fun u v => u + v

/-- Multiplication by `n` on first-order jets at `O`. -/
theorem FormalJetAtO.nsmul_eq_natCast_mul
    (W : WeierstrassCurve K) (n : ℕ) (v : FormalJetAtO W) :
    n • v = (n : K) * v := by
  -- This is just `nsmul_eq_mul` for the additive group/vector space `K`.
  simpa [FormalJetAtO] using (nsmul_eq_mul n v)

end

end WeierstrassCurve
```

This does not pretend to be the full formal group.  It isolates the exact tangent theorem the separability proof needs.  Later, if you construct `W.formalGroup : FormalGroup K`, you can prove this jet API from it and deprecate the local version.

### What remains after the jet API

The jet itself is trivial.  The real work is proving that the actual curve maps into it correctly:

```lean
/-- A dual-number point sufficiently near `O` has a formal parameter coefficient. -/
def tangentCoeffAtO
    (W : WeierstrassCurve K)
    (Pε : /* projective W-point over TrivSqZeroExt K K reducing to O */) : K :=
  sorry

/-- Addition of dual-number points near `O` linearizes to addition of tangent coefficients. -/
theorem tangentCoeffAtO_add
    (W : WeierstrassCurve K) [W.IsElliptic]
    (Pε Qε : /* near-O dual points */) :
    tangentCoeffAtO W (Pε + Qε)
      = tangentCoeffAtO W Pε + tangentCoeffAtO W Qε := by
  sorry
```

This is much smaller than full power-series associativity, but it still needs either projective coordinates over `TrivSqZeroExt` or explicit near-`O` formulas.

---

## (b) Can we avoid the full formal group and prove `d[n]|_O = n` directly?

Yes.  This is the route I recommend for the next Lean implementation attempt.

There are two direct variants.

### Variant B1: first-order projective coordinates near `O`

Use projective coordinates.  The point at infinity is

```text
O = [0 : 1 : 0].
```

The standard local parameters are

```text
t = -X/Y,
w = -Z/Y.
```

For a first-order point near `O` over `K[ε]/ε²`, the curve equation forces `w = 0` to first order, so it has the form

```text
[-ε*v : 1 : 0]
```

up to the chosen sign convention for `t`.  The first-order tangent scalar is `v`.

Minimal theorem:

```lean
/-- First-order projective points near `O` are parametrized by one scalar. -/
def OJetPoint (W : WeierstrassCurve K) (v : K) :
    /* projective point over TrivSqZeroExt K K */ :=
  -- schematic: [-ε*v : 1 : 0]
  sorry

/-- The addition law near `O` has linear part addition. -/
theorem OJetPoint_add
    (W : WeierstrassCurve K) [W.IsElliptic]
    (u v : K) :
    OJetPoint W u + OJetPoint W v = OJetPoint W (u + v) := by
  -- Prove by expanding the projective addition formula over dual numbers.
  -- Since ε² = 0, all higher terms vanish.
  sorry

/-- Therefore `[n]` on first-order points near `O` is multiplication by `(n : K)`. -/
theorem OJetPoint_nsmul
    (W : WeierstrassCurve K) [W.IsElliptic]
    (n : ℕ) (v : K) :
    n • OJetPoint W v = OJetPoint W ((n : K) * v) := by
  induction n with
  | zero => simp [OJetPoint]
  | succ n ih =>
      -- use `OJetPoint_add` and the induction hypothesis
      sorry
```

This avoids infinite power series entirely.

The catch is that Mathlib does not currently expose a projective Weierstrass group law over arbitrary commutative rings.  If there are projective addition formulas only over fields, you will need to write the tiny near-`O` dual-number addition formula yourself or formalize a ring-level projective formula.

### Variant B2: invariant differential

The invariant differential is

```text
ω = dx / (2y + a₁x + a₃).
```

The usual proof is:

```text
[n]^*ω = n · ω.
```

Then `d[n]|_O = n` follows because `ω` trivializes the cotangent line at `O`.

This avoids explicit full formal group law, but in current Mathlib it is probably not shorter.  You would need:

* a definition of regular differentials or at least Kähler differentials on the coordinate ring;
* the invariant differential `ω` as a regular differential on the smooth cubic;
* pullback of differentials by `[n]`;
* proof that pullback by translation fixes `ω`;
* proof that `[n]^*ω = nω`.

That is elegant but heavy.  It is more general algebraic geometry than the separability proof needs.

### Variant B3: formal logarithm

In characteristic zero, the formal logarithm gives

```text
log([n](T)) = n * log(T),
```

hence the linear coefficient is `n`.  This is very clean mathematically in the application if the field really has characteristic zero.

But Lean-wise, it still requires constructing the Weierstrass formal group law or at least its invariant differential as a power series.  It also introduces denominators, so it is less ideal if the theorem statement is only `(n : K) ≠ 0` in arbitrary characteristic.

Conclusion for (b): **yes, avoid the full formal group; prove the first-order projective/tangent theorem directly.**  Do not start with invariant differentials unless the project later needs them anyway.

---

## (c) Can we prove derivative nonvanishing directly from division-polynomial recurrences?

I would not choose this as the main route.

A recurrence-only proof would need to show that a dual-number root of `preΨ'_n` cannot exist.  Differentiating the recurrence gives identities involving neighboring `preΨ'` values and their derivatives.  At a root of `preΨ'_n`, the recurrence rarely isolates the derivative of `preΨ'_n` alone; it also requires strong coprimality/rank-of-apparition facts for neighboring indices and small strata.

The induction would start needing statements like:

```lean
IsCoprime (W.preΨ' m) (W.preΨ' r)
IsCoprime (W.preΨ' m) W.Ψ₂Sq
IsCoprime (W.preΨ' m) W.Ψ₃
IsCoprime (W.preΨ' m) W.preΨ₄
```

and finally a derivative/root exclusion that is equivalent to separability.  This is the formal-group theorem reappearing in recurrence language.

There is a very useful recurrence proof for **two-torsion exclusion**:

```lean
(W.preΨ' n).IsRoot x → W.Ψ₂Sq.eval x ≠ 0
```

because setting `Ψ₂Sq.eval x = 0` collapses the EDS to explicit closed forms.  But derivative nonvanishing is harder: it is first-order data, and first-order data is exactly tangent/formal-group data.

So route (c) is possible in principle, but I expect it to be longer and more fragile than the first-order geometric bridge.

---

## (d) Does the derivative of `x([n]P)=φ_n/ψ_n²` route work?

As stated, I think it is the wrong chart at the critical point.

When `ψ_n(P)=0`, `[n]P = O`.  The affine `x`-coordinate of `[n]P` has a pole at `O`, so the formula

```text
x([n]P) = φ_n(P) / ψ_n(P)^2
```

is not a regular coordinate near the image point.  Differentiating the quotient

```text
(dφ_n * ψ_n² - φ_n * d(ψ_n²)) / ψ_n⁴
```

at `ψ_n(P)=0` is not a valid affine tangent calculation; the denominator vanishes.  The correct local coordinate at the image is not `x`, but

```text
t = -X/Y
```

or an equivalent projective/formal parameter at `O`.

To use division-polynomial coordinate formulas productively, you would need the **projective** multiplication-by-`n` formula, including the `y`/`ω_n` coordinate, not only `φ_n` and `ψ_n²`.  Mathlib’s division-polynomial file even notes `ω_n` as TODO in the docs, so this is not presently packaged.

The usable theorem would be closer to:

```lean
/-- Homogeneous/projective division-polynomial formula for `[n]`, valid over a commutative ring. -/
theorem projective_nsmul_eq_division_polynomials
    (W : WeierstrassCurve R) (n : ℕ) :
    -- schematic: [n](X:Y:Z) = (Φₙ Ψₙ : Ωₙ : Ψₙ³) or equivalent homogeneous coordinates
    True := by
  sorry
```

Then at a dual-number point with `Ψₙ = ε*a` and `Φₙ` a unit/nonzero scalar, one computes the formal parameter of the image near `O` and sees its first-order coefficient.  But this is effectively building the functor-of-points bridge for `[n]` over dual numbers.

So route (d) can work only after adding projective division-polynomial formulas over rings.  Without them, it risks circularity because:

* `φ_n(P) ≠ 0` at `ψ_n(P)=0` is already a no-common-root theorem;
* showing the order of vanishing of `ψ_n` is exactly one is separability itself;
* affine `x` is not a regular coordinate at `O`.

---

## Critical missing piece by route

| Route | Minimal missing piece | Difficulty | Comment |
|---|---:|---:|---|
| Full `W.formalGroup : FormalGroup K` | Construct Silverman formal group law as power series and prove FGL axioms | High | Clean long-term object, but too big for just separability |
| First-order formal jet | Dual/projective addition near `O`: `OJet u + OJet v = OJet (u+v)` | Medium | Best targeted route for `d[n]|_O = n` |
| Invariant differential | Pullback of `ω` under `[n]`, regular differentials on the curve | High | Elegant but requires differential infrastructure |
| Formal logarithm | Full formal group plus log/exp over char 0 | High | Good only for char 0; theorem wants `(n : K) ≠ 0` |
| Recurrence derivative induction | General derivative coprimality from EDS recurrence | High/unclear | Likely re-proves formal group in disguise |
| Affine quotient derivative `φ/ψ²` | Replace affine quotient by projective local parameter at `O` | High | Needs `ω_n`/projective division-polynomial formulas |

---

## Recommended architecture for Round 1 Lean design

I would not define `W.formalGroup` first.  I would define the exact interface needed by the proof, then later show it follows from a full formal group if desired.

### File 1: first-order projective/tangent API

```lean
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

open Polynomial

namespace WeierstrassCurve

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]

/-- First-order tangent scalar at the origin. -/
abbrev FormalJetAtO (W : WeierstrassCurve K) := K

/-- A schematic first-order point reducing to `O`.  Implement this either with projective
coordinates over `TrivSqZeroExt K K`, or as a local structure carrying the coordinate formula. -/
structure OJetPoint (W : WeierstrassCurve K) where
  coeff : K
  -- projective coordinates and proof of the Weierstrass equation can be added here
  -- if/when the ring-level projective point structure is introduced.

@[simp] theorem OJetPoint.ext_iff {W : WeierstrassCurve K} {P Q : OJetPoint W} :
    P = Q ↔ P.coeff = Q.coeff := by
  constructor
  · intro h; simpa [h]
  · intro h; cases P; cases Q; simp at h; simp [h]

/-- First-order addition at the origin. -/
def OJetPoint.add (W : WeierstrassCurve K) (P Q : OJetPoint W) : OJetPoint W :=
  ⟨P.coeff + Q.coeff⟩

/-- The theorem that must eventually be connected to actual curve addition. -/
theorem OJetPoint_add_coeff
    (W : WeierstrassCurve K) (P Q : OJetPoint W) :
    (OJetPoint.add W P Q).coeff = P.coeff + Q.coeff := rfl

/-- Multiplication by `n` on first-order jets. -/
def OJetPoint.nsmul (W : WeierstrassCurve K) (n : ℕ) (P : OJetPoint W) : OJetPoint W :=
  ⟨(n : K) * P.coeff⟩

@[simp] theorem OJetPoint.nsmul_coeff
    (W : WeierstrassCurve K) (n : ℕ) (P : OJetPoint W) :
    (OJetPoint.nsmul W n P).coeff = (n : K) * P.coeff := rfl

end

end WeierstrassCurve
```

This file is intentionally “honest fake infrastructure”: it states the tangent API in the smallest possible form.  The next files replace schematic parts by actual projective dual-number statements.

### File 2: translation to `O`

```lean
namespace WeierstrassCurve

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- A first-order deformation of an affine non-2-torsion point. -/
structure AffineDualPointAt (x y : K) where
  dx : K
  dy : K
  equation_dual :
    -- use your existing `equation_dual_iff` theorem here
    True

/-- Translation by `-P` sends a deformation of `P` to a first-order point at `O`. -/
def translateToOJet
    {x y : K}
    (hP : W.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (Pε : AffineDualPointAt W x y) :
    OJetPoint W := by
  -- This is where actual addition or explicit translation formulas enter.
  -- The output coefficient must be a nonzero scalar multiple of `Pε.dx`.
  exact ⟨Pε.dx⟩

/-- Nonzero `dx` gives nonzero formal tangent after translation. -/
theorem translateToOJet_coeff_ne_zero
    {x y : K}
    (hP : W.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (Pε : AffineDualPointAt W x y)
    (hdx : Pε.dx ≠ 0) :
    (translateToOJet W hP hY Pε).coeff ≠ 0 := by
  -- If the actual translation coefficient is `unit * dx`, this is immediate.
  simpa [translateToOJet] using hdx

end

end WeierstrassCurve
```

The placeholder `exact ⟨Pε.dx⟩` is not the final formula; the point is that this file isolates the translation calculation.  In the real proof, the coefficient will likely be `unit * dx`, where the unit involves `polynomialY.evalEval x y`.

### File 3: division-polynomial bridge over dual numbers

```lean
namespace WeierstrassCurve

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- If the reduced division polynomial vanishes on a non-2-torsion dual deformation,
then the translated first-order point lies in the infinitesimal kernel of `[n]`. -/
theorem preΨ'_dual_root_translateToOJet_nsmul_eq_zero
    {n : ℕ} {x y : K}
    (hP : W.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (Pε : AffineDualPointAt W x y)
    (hpre :
      -- use your existing `MultipleRootBridge` / dual aeval statement
      True) :
    (OJetPoint.nsmul W n (translateToOJet W hP hY Pε)).coeff = 0 := by
  -- This is the critical bridge.
  -- It needs either projective division-polynomial formulas over `TrivSqZeroExt K K`,
  -- or a ring-level functor-of-points group law.
  sorry

/-- The final tangent contradiction. -/
theorem no_nonzero_dual_preΨ'_root_of_natCast_ne_zero
    {n : ℕ} (hn : (n : K) ≠ 0) {x y : K}
    (hP : W.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (Pε : AffineDualPointAt W x y)
    (hdx : Pε.dx ≠ 0)
    (hpre : True) : False := by
  have hzero := preΨ'_dual_root_translateToOJet_nsmul_eq_zero
    (W := W) (n := n) hP hY Pε hpre
  have hcoeff_ne := translateToOJet_coeff_ne_zero (W := W) hP hY Pε hdx
  have : (n : K) * (translateToOJet W hP hY Pε).coeff = 0 := by
    simpa [OJetPoint.nsmul] using hzero
  have hcoeff_zero : (translateToOJet W hP hY Pε).coeff = 0 :=
    (mul_eq_zero.mp this).resolve_left hn
  exact hcoeff_ne hcoeff_zero

end

end WeierstrassCurve
```

This is the exact shape of the final nonzero-tangent contradiction.  Notice that it does not require a full `FormalGroup` instance; it requires only the first-order behavior of `[n]` and the division-polynomial bridge.

---

## How to reuse your existing `FormalGroup` theorem

If you still want to use your existing `FormalGroup` structure, add an adapter theorem rather than building the full `W.formalGroup` immediately:

```lean
/-- Any actual formal group attached to `W` induces the first-order jet API. -/
theorem formalGroup_to_OJet_nsmul
    (W : WeierstrassCurve K)
    (FG : FormalGroup K)
    (hFG_linearizes_W :
      -- `FG` is the formal completion of `W` at `O`, at least to first order.
      True)
    (n : ℕ) (v : K) :
    -- schematic: `[n]` on the W-jet has coefficient `(n : K) * v`
    True := by
  -- use `formalNsmul_coeff_one FG n`
  sorry
```

This keeps your `FormalGroup` work useful but prevents it from becoming a blocker.  The actual separability proof can depend on the first-order jet theorem; the full `W.formalGroup` can be proved later and shown to imply that theorem.

---

## Round-1 recommendation

For the next implementation round, I would **not** try to write `W.formalGroup : FormalGroup K` first.  I would write the following theorem as the central target:

```lean
theorem preΨ'_dual_root_translateToOJet_nsmul_eq_zero
    (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} {x y : K}
    (hP : W.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (Pε : AffineDualPointAt W x y)
    (hpre : aeval (/* x + ε*dx */) (W.preΨ' n) = 0) :
    (n : K) * (translateToOJet W hP hY Pε).coeff = 0
```

Then split it into two independent subgoals:

1. **Translation calculation:** `translateToOJet` is a unit multiple of the original `dx` for non-2-torsion points.
2. **Division-polynomial/projective bridge:** `preΨ'_n` vanishing over dual numbers means `[n](Pε)` reduces to `O` and has formal jet equal to `n` times the translated jet.

The second subgoal is the hard one.  It is also the subgoal that a full formal group law alone does not solve unless you can connect `preΨ'_n` to the actual `[n]` functor over dual numbers.  Therefore, architecturally, the projective/homogeneous division-polynomial bridge is the highest-value next piece.

## Final answer by route

* **(a) Full formal group law:** correct but heavy; not minimal.  Use only if you want a reusable formal-group library.
* **(b) Direct `d[n]|_O = n`:** yes, best route.  Prove it as a first-order jet theorem, not as a full FGL instance.
* **(c) Direct recurrence derivative proof:** not recommended; derivative data forces tangent/formal content back in.
* **(d) Differentiate `φ/ψ²`:** not in affine `x`; at `ψ=0`, `[n]P=O`, so the correct chart is the formal/projective parameter at `O`.  Needs projective division-polynomial formulas, not just `mk_φ` and `mk_Ψ_sq`.

The main architectural point is: **separate the tangent theorem from the full formal group.**  Build the first-order Weierstrass jet and the dual-number projective division-polynomial bridge first.  Package it as `W.formalGroup` only after the separability proof no longer depends on that packaging decision.
