# Q3007 dm-codex2: N10 Kubert residual narrowing

Namespace targets:

```lean
namespace MazurProof.KubertBridgeN10
```

Files:

```text
FLT/Assumptions/MazurProof/KubertBridgeN10.lean
FLT/Assumptions/MazurProof/KubertTateCommon.lean
FLT/Assumptions/MazurProof/KubertBridgeN12.lean
```

I could not fetch the local WIP files through the GitHub connector, so this answer is keyed to the self-contained status in the prompt. The formulas below should be checked against the exact local definitions of `A10`, `B10`, `Delta10`, `tateC10_b`, and `tateC10_c` before being used as final theorem statements.

## Part 1. Variable change from Tate C10 row to short form

### 1.1 Standard long-Weierstrass to short variable change

For a general Weierstrass equation

```text
y² + a1*x*y + a3*y = x³ + a2*x² + a4*x + a6
```

with invariants

```text
b2 = a1² + 4a2
b4 = 2a4 + a1a3
b6 = a3² + 4a6
c4 = b2² - 24b4
c6 = -b2³ + 36b2b4 - 216b6
```

the standard rational variable change to

```text
shortW (-27*c4) (-54*c6)
```

is

```text
u = 1/6
r = -b2/12
s = -a1/2
t = (a1*b2 - 12*a3)/24.
```

This is the usual `x = u² x' + r`, `y = u³ y' + u² s x' + t` convention used by `WeierstrassCurve.variableChange_*`. With `u=1/6`, the intermediate coefficients `-c4/48`, `-c6/864` scale to `-27*c4`, `-54*c6`.

For Tate normal form

```text
tateW b c : y² + (1-c)xy - b*y = x³ - b*x²
```

the coefficients are

```text
a1 = 1 - c
a2 = -b
a3 = -b
a4 = 0
a6 = 0
```

so

```text
b2 = (1-c)^2 - 4b
b4 = b(c-1)
b6 = b^2
b8 = -b^3
c4 = b2^2 - 24*b4
c6 = -b2^3 + 36*b2*b4 - 216*b6.
```

### 1.2 Common definitions to put in `KubertTateCommon.lean`

These are generic enough to share between N10 and N12.

```lean
import Mathlib.Tactic

namespace MazurProof.KubertTateCommon

noncomputable def tate_c4 (b c : ℚ) : ℚ :=
  (tate_b2 b c) ^ 2 - 24 * tate_b4 b c

noncomputable def tate_c6 (b c : ℚ) : ℚ :=
  - (tate_b2 b c) ^ 3 + 36 * tate_b2 b c * tate_b4 b c - 216 * tate_b6 b

/-- Standard variable change from Tate normal form to short Weierstrass form. -/
noncomputable def tateToShortVC (b c : ℚ) : WeierstrassCurve.VariableChange ℚ :=
  WeierstrassCurve.VariableChange.mk
    (1 / 6)
    (-(tate_b2 b c) / 12)
    (-(1 - c) / 2)
    (((1 - c) * tate_b2 b c + 12 * b) / 24)

/-- The expected short coefficient `A=-27*c4`. -/
noncomputable def tateShortA (b c : ℚ) : ℚ :=
  -27 * tate_c4 b c

/-- The expected short coefficient `B=-54*c6`. -/
noncomputable def tateShortB (b c : ℚ) : ℚ :=
  -54 * tate_c6 b c

end MazurProof.KubertTateCommon
```

The `+ 12*b` in the last coordinate is because `a3=-b`, hence

```text
t = (a1*b2 - 12*a3)/24 = ((1-c)*b2 + 12b)/24.
```

### 1.3 Coefficient theorem skeleton

Use this theorem first, before mentioning C10-specific `A10/B10`.

```lean
import Mathlib.Tactic
-- import local Tate definitions

namespace MazurProof.KubertTateCommon

/-- Generic Tate-to-short coefficient equality. -/
theorem tateW_variableChange_tateToShortVC_eq_short
    (b c : ℚ) :
    (tateW b c).variableChange (tateToShortVC b c) =
      shortW (tateShortA b c) (tateShortB b c) := by
  -- Expected proof shape.  If `ext` does not pick Weierstrass fields,
  -- use `cases`/field projections or the local ext theorem for `WeierstrassCurve`.
  ext <;>
    simp [tateToShortVC, tateShortA, tateShortB, tate_c4, tate_c6,
      tateW, tate_b2, tate_b4, tate_b6] <;>
    norm_num <;>
    ring

/-- Discriminant is scaled by a nonzero twelfth power under the above variable change. -/
theorem tateToShort_discriminant_ne_zero_iff
    (b c : ℚ) :
    (shortW (tateShortA b c) (tateShortB b c)).Δ ≠ 0 ↔
      (tateW b c).Δ ≠ 0 := by
  -- Route A: use Mathlib variable-change discriminant formula.
  --   `Δ' = u^(-12) * Δ` or `u^12 * Δ' = Δ`, depending orientation.
  -- With `u=1/6`, nonzero is immediate.
  -- Route B: unfold both discriminants and prove by ring_nf:
  --   Δ(shortW(-27c4,-54c6)) = 6^12 * Δ(tateW b c)
  -- Then use `mul_ne_zero` with `norm_num`.
  constructor
  · intro hs ht
    have hscale :
        (shortW (tateShortA b c) (tateShortB b c)).Δ =
          (6 : ℚ) ^ 12 * (tateW b c).Δ := by
      simp [tateShortA, tateShortB, tate_c4, tate_c6,
        tateW, tate_b2, tate_b4, tate_b6]
      ring
    exact hs (by rw [hscale, ht, mul_zero])
  · intro ht hs
    have hscale :
        (shortW (tateShortA b c) (tateShortB b c)).Δ =
          (6 : ℚ) ^ 12 * (tateW b c).Δ := by
      simp [tateShortA, tateShortB, tate_c4, tate_c6,
        tateW, tate_b2, tate_b4, tate_b6]
      ring
    apply ht
    have h6 : ((6 : ℚ) ^ 12) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp (by simpa [hscale] using hs)).resolve_left h6

end MazurProof.KubertTateCommon
```

If `shortW(A,B).Δ` is not definitionally the `-16*(4A^3+27B^2)` convention, the proof above will show the mismatch. Use the local `#check shortW` and unfold its discriminant before trusting the scaling theorem.

### 1.4 C10-specialized theorem

This is the narrow residual interface to add in `KubertBridgeN10.lean`. It should be a theorem, not an axiom, if the local definitions of `A10/B10` match the standard invariants.

```lean
namespace MazurProof.KubertBridgeN10

open MazurProof.KubertTateCommon

/-- C10 Tate row converted to the short model used by the N10 square obstruction. -/
theorem tateC10_to_shortW_coefficients
    {q : ℚ}
    (hden : tateC10_den q ≠ 0) :
    (tateW (tateC10_b q) (tateC10_c q)).variableChange
        (tateToShortVC (tateC10_b q) (tateC10_c q)) =
      shortW (A10 q) (B10 q) := by
  -- First reduce to the generic theorem.
  have hshort :=
    tateW_variableChange_tateToShortVC_eq_short
      (tateC10_b q) (tateC10_c q)
  -- Then prove `A10 q = tateShortA ...` and `B10 q = tateShortB ...`.
  -- This is pure rational-function algebra using `hden`.
  rw [hshort]
  congr <;>
    unfold A10 B10 tateC10_b tateC10_c tateC10_den
      tateShortA tateShortB tate_c4 tate_c6
      tate_b2 tate_b4 tate_b6 <;>
    field_simp [hden] <;>
    ring

/-- Nonzero short discriminant follows from nonzero Tate discriminant and denominator. -/
theorem Delta10_ne_zero_of_tate_delta
    {q : ℚ}
    (hden : tateC10_den q ≠ 0)
    (hDeltaTate : (tateW (tateC10_b q) (tateC10_c q)).Δ ≠ 0) :
    Delta10 q ≠ 0 := by
  -- If `Delta10 q` is definitionally `(shortW (A10 q) (B10 q)).Δ`, use coefficient theorem + scaling.
  -- If `Delta10` is a polynomial with denominator cleared, this is pure algebra using `hden`.
  -- Expected proof:
  have hshortDelta : (shortW (A10 q) (B10 q)).Δ ≠ 0 := by
    have hiff :=
      tateToShort_discriminant_ne_zero_iff (tateC10_b q) (tateC10_c q)
    -- rewrite short coefficients to `A10/B10`
    -- exact hiff.mpr hDeltaTate after rewriting
    sorry
  -- Then unfold `Delta10` and compare to the short discriminant.
  -- Example if `Delta10 = (shortW ...).Δ`:
  -- simpa [Delta10] using hshortDelta
  sorry

end MazurProof.KubertBridgeN10
```

The two `sorry`s above mark a local-definition dependency, not a new mathematical residual. If `Delta10` is denominator-cleared rather than the actual discriminant, the theorem should state the exact clearing factor:

```lean
theorem shortW_A10_B10_delta_eq_clearing_factor
    (q : ℚ) :
    (shortW (A10 q) (B10 q)).Δ =
      Delta10 q / (tateC10_den q) ^ N := by
  field_simp [tateC10_den]
  ring
```

for the actual exponent `N` visible from the local definitions. Then `Delta10_ne_zero_of_tate_delta` follows from `hden`.

### 1.5 CAS verification script for hidden `A10/B10` definitions

Because I cannot see the local `A10/B10`, verify the formulas before committing Lean code.

```python
import sympy as sp
q = sp.symbols('q')

# Fill these with the exact local definitions from KubertBridgeN10.lean.
den = sp.sympify('REPLACE_ME')
b = sp.sympify('REPLACE_ME')
c = sp.sympify('REPLACE_ME')
A10 = sp.sympify('REPLACE_ME')
B10 = sp.sympify('REPLACE_ME')
Delta10 = sp.sympify('REPLACE_ME')

b2 = (1-c)**2 - 4*b
b4 = b*(c-1)
b6 = b**2
c4 = b2**2 - 24*b4
c6 = -b2**3 + 36*b2*b4 - 216*b6
Astd = -27*c4
Bstd = -54*c6

print('A diff numerator:', sp.factor(sp.together(A10 - Astd).as_numer_denom()[0]))
print('B diff numerator:', sp.factor(sp.together(B10 - Bstd).as_numer_denom()[0]))

short_delta = -16*(4*A10**3 + 27*B10**2)
print('short_delta / Delta10:', sp.factor(sp.together(short_delta / Delta10)))
```

If the first two numerators are zero, the variable change above is exactly the desired change. If they are nonzero by a square scaling, your `shortW(A10 q)(B10 q)` is a further scaling of the standard short model; add a final scaling variable change `u` with `A/u^4`, `B/u^6` as needed.

## Part 2. Narrowing the order-10 Tate normal-form residual

This should mirror the N12 `TateNormalFormAtOrder12` construction. It is an integration/normalization task, not a new C10 table-algebra residual.

### 2.1 Exact local lemmas to add

#### Lemma A: translate an order-10 point to the origin

Pure variable-change/additive-equivalence; this is not mathematically hard.

```lean
namespace MazurProof.KubertBridgeN10

noncomputable def translatePointToOriginVC (x0 y0 : ℚ) :
    WeierstrassCurve.VariableChange ℚ :=
  WeierstrassCurve.VariableChange.mk 1 x0 0 y0

structure TranslatedOriginOrder10 where
  W : WeierstrassCurve ℚ
  hO : WeierstrassCurve.Affine.Nonsingular (WeierstrassCurve.toAffine W) 0 0
  hOrder : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) = 10
  h6 : W.a₆ = 0

/-- Translation sends an exact order-10 affine point to `(0,0)`. -/
theorem translate_order10_point_to_origin
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 10) :
    TranslatedOriginOrder10 := by
  -- Same proof template as the checked N12 theorem `translate_order12_point_to_origin`.
  -- Use `translatePointToOriginVC`, `affinePointAddEquivOfVariableChange`, and
  -- `addOrderOf_apply_addEquiv`.
  -- The `a₆=0` field follows because `(0,0)` lies on the translated curve.
  -- This is checkable by the N12 template.
  exact translate_orderN_point_to_origin_template 10 E P hP

end MazurProof.KubertBridgeN10
```

If you do not have a generic template, copy the N12 proof and replace `12` by `10`. The only order-specific line is the final `rw [hP]`.

#### Lemma B: origin order 10 implies `a₃ ≠ 0`

Pure group-law/negation. If `a₃=0`, then `(0,0)` equals its inverse on a curve with `a₆=0`, so order divides `2`, contradiction to exact order `10`.

```lean
namespace MazurProof.KubertBridgeN10

/-- At an origin point, exact order 10 forces `a₃ ≠ 0`. -/
theorem origin_a3_ne_zero_of_addOrderOf_eq_10
    (W : WeierstrassCurve ℚ)
    (hO : WeierstrassCurve.Affine.Nonsingular (WeierstrassCurve.toAffine W) 0 0)
    (hOrder : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) = 10) :
    W.a₃ ≠ 0 := by
  intro h3
  let P := WeierstrassCurve.Affine.Point.some 0 0 hO
  have hPneg : P = -P := by
    -- Negation formula at `(0,0)` is `(0,-a3)`, so `a3=0` gives self-negation.
    ext <;> simp [P, h3]
  have h2P : (2 : ℕ) • P = 0 := by
    rw [two_nsmul]
    exact eq_neg_iff_add_eq_zero.mp hPneg
  have hdiv : addOrderOf P ∣ 2 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h2P
  rw [hOrder] at hdiv
  norm_num at hdiv

end MazurProof.KubertBridgeN10
```

If the exact N12 theorem already exists for all `n` or can be copied, this should compile with the local affine point `ext/simp` adjustments.

#### Lemma C: kill `a₄`, preserve origin/order 10

Pure coefficient algebra plus additive equivalence. Reuse the N12 `killA4VC` unchanged.

```lean
namespace MazurProof.KubertBridgeN10

noncomputable def killA4VC (W : WeierstrassCurve ℚ) (h3 : W.a₃ ≠ 0) :
    WeierstrassCurve.VariableChange ℚ :=
  WeierstrassCurve.VariableChange.mk 1 0 (W.a₄ / W.a₃) 0

noncomputable abbrev killA4W (W : WeierstrassCurve ℚ) (h3 : W.a₃ ≠ 0) :
    WeierstrassCurve ℚ :=
  W.variableChange (killA4VC W h3)

theorem killA4W_a4_eq_zero (W : WeierstrassCurve ℚ) (h3 : W.a₃ ≠ 0) :
    (killA4W W h3).a₄ = 0 := by
  rw [killA4W, killA4VC, WeierstrassCurve.variableChange_a₄]
  field_simp [h3]
  ring

theorem killA4W_a6_eq_zero
    (W : WeierstrassCurve ℚ) (h3 : W.a₃ ≠ 0) (h6 : W.a₆ = 0) :
    (killA4W W h3).a₆ = 0 := by
  rw [killA4W, killA4VC, WeierstrassCurve.variableChange_a₆]
  simp [h6]

/-- Killing `a₄` preserves exact order 10 of the origin. -/
theorem killA4W_origin_order10
    (W : WeierstrassCurve ℚ)
    (hO : WeierstrassCurve.Affine.Nonsingular (WeierstrassCurve.toAffine W) 0 0)
    (h6 : W.a₆ = 0)
    (h3 : W.a₃ ≠ 0)
    (hOrder : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) = 10) :
    ∃ hO' : WeierstrassCurve.Affine.Nonsingular
      (WeierstrassCurve.toAffine (killA4W W h3)) 0 0,
      addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO') = 10 := by
  -- Copy the N12 proof: variable change has `r=t=0`, so the origin maps to origin,
  -- and an additive equivalence preserves `addOrderOf`.
  exact killA4W_origin_order_template 10 W hO h6 h3 hOrder

end MazurProof.KubertBridgeN10
```

#### Lemma D: exclude `a₂=0`

This is the same genuine normal-form residual as in N12, but it can be shared. If `a₂=a₄=a₆=0`, then `(0,0)` has order dividing `3`; exact order `10` is impossible.

Use a common theorem in `KubertTateCommon.lean`:

```lean
namespace MazurProof.KubertTateCommon

/-- Shared hard affine group-law lemma: with `a₂=a₄=a₆=0`, origin has order dividing 3. -/
def OriginOrderDividesThreeWhenA2A4A6ZeroStatement : Prop :=
  ∀ (W : WeierstrassCurve ℚ)
    (hO : WeierstrassCurve.Affine.Nonsingular (WeierstrassCurve.toAffine W) 0 0),
    W.a₂ = 0 → W.a₄ = 0 → W.a₆ = 0 →
      (3 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 hO = 0

end MazurProof.KubertTateCommon
```

Then N10 consumes it:

```lean
namespace MazurProof.KubertBridgeN10

/-- Exact order 10 excludes `a₂=0` once `a₄=a₆=0`. -/
theorem origin_a2_ne_zero_of_a4_a6_origin_order10
    (h3div : KubertTateCommon.OriginOrderDividesThreeWhenA2A4A6ZeroStatement)
    (W : WeierstrassCurve ℚ)
    (hO : WeierstrassCurve.Affine.Nonsingular (WeierstrassCurve.toAffine W) 0 0)
    (h4 : W.a₄ = 0) (h6 : W.a₆ = 0)
    (hOrder : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) = 10) :
    W.a₂ ≠ 0 := by
  intro h2
  have h3P : (3 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 hO = 0 :=
    h3div W hO h2 h4 h6
  have hdiv : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) ∣ 3 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr h3P
  rw [hOrder] at hdiv
  norm_num at hdiv

end MazurProof.KubertBridgeN10
```

Classification:

```text
OriginOrderDividesThreeWhenA2A4A6ZeroStatement = genuine elliptic-curve group-law residual.
origin_a2_ne_zero_of_a4_a6_origin_order10 = pure order-theory wrapper once that residual exists.
```

#### Lemma E: scale to Tate normal form

Pure coefficient algebra; same as N12 and independent of order value.

After `a₄=a₆=0`, `a₃≠0`, and `a₂≠0`, set

```text
u = a₃/a₂, r=s=t=0.
```

Then

```text
a1' = a1*a2/a3
a2' = a2^3/a3^2
a3' = a2^3/a3^2
a4' = 0
a6' = 0.
```

For Tate form with coefficients

```text
a1 = 1-c, a2=-b, a3=-b, a4=0, a6=0
```

set

```text
b = - a₂^3 / a₃^2
c = 1 - a₁*a₂/a₃.
```

```lean
namespace MazurProof.KubertTateCommon

noncomputable def scaleToTateVC
    (W : WeierstrassCurve ℚ) (h2 : W.a₂ ≠ 0) (h3 : W.a₃ ≠ 0) :
    WeierstrassCurve.VariableChange ℚ :=
  WeierstrassCurve.VariableChange.mk (W.a₃ / W.a₂) 0 0 0

noncomputable def tate_b_of_W (W : WeierstrassCurve ℚ) : ℚ :=
  - W.a₂ ^ 3 / W.a₃ ^ 2

noncomputable def tate_c_of_W (W : WeierstrassCurve ℚ) : ℚ :=
  1 - W.a₁ * W.a₂ / W.a₃

theorem scaleToTateW_eq_tateW
    (W : WeierstrassCurve ℚ)
    (h2 : W.a₂ ≠ 0) (h3 : W.a₃ ≠ 0)
    (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) :
    W.variableChange (scaleToTateVC W h2 h3) =
      tateW (tate_b_of_W W) (tate_c_of_W W) := by
  ext <;>
    simp [scaleToTateVC, tate_b_of_W, tate_c_of_W, tateW,
      h2, h3, h4, h6] <;>
    field_simp [h2, h3] <;>
    ring

end MazurProof.KubertTateCommon
```

Classification: pure coefficient algebra.

### 2.2 Narrow order-10 Tate-normal-form residual interface

The N10 analog of N12’s `TateNormalFormAtOrder12` should only need the shared `a₂=0 -> 3P=0` residual. Suggested statement:

```lean
namespace MazurProof.KubertBridgeN10

structure TateNormalFormAtOrder10 (E : WeierstrassCurve ℚ) where
  b c : ℚ
  hb : b ≠ 0
  hDelta : (tateW b c).Δ ≠ 0
  P : (E⁄ℚ).Point
  hP : addOrderOf P = 10
  φ : (E⁄ℚ).Point ≃+ WeierstrassCurve.Affine.Point (tateW b c)
  hφP : φ P = tateOriginAffine b c hb

/-- Narrow residual interface: order-10 point gives Tate normal form. -/
def TateNormalFormAtOrder10Statement : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point),
    addOrderOf P = 10 →
      ∃ T : TateNormalFormAtOrder10 E, True

end MazurProof.KubertBridgeN10
```

If you do not want an `AddEquiv` in the structure yet, weaken to `AddMonoidHom + Function.Injective`; but for normal-form transport, the N12 template likely already has an additive equivalence from variable changes, so `≃+` is the cleanest.

### 2.3 How this reduces the original `kubert_C10_square` residual

The remaining C10 residual should be split into two narrow statements:

1. **Tate normal-form residual**: order-10 point on an arbitrary curve transports to Tate form.
2. **Tate-to-short algebra residual**: the C10 Tate row variable-changes to `shortW(A10 q)(B10 q)` and gives the square condition.

The second is mostly checked algebra if `A10/B10` are the standard `-27c4/-54c6` specializations. The final square statement should consume the row theorem and the coefficient theorem:

```lean
namespace MazurProof.KubertBridgeN10

/-- Narrow C10 short-square algebra from the checked Tate row. -/
def C10TateRowToShortSquareStatement : Prop :=
  ∀ {b c : ℚ}
    (hb : b ≠ 0)
    (hDelta : (tateW b c).Δ ≠ 0)
    (hOrder : addOrderOf (tateOriginAffine b c hb) = 10),
    ∃ q s : ℚ,
      Delta10 q ≠ 0 ∧
      s ^ 2 = (A10 q) ^ 2 - 4 * B10 q

end MazurProof.KubertBridgeN10
```

Then the full original residual is only the composition of:

```text
ZMod 2 × ZMod 10 injection
  -> choose point P of order 10                     [group/ZMod extraction]
  -> TateNormalFormAtOrder10Statement              [normal-form residual]
  -> C10TateRowToShortSquareStatement              [Tate row + short algebra]
```

Do not keep one global `kubert_C10_square` axiom. Replace it by those two narrow interfaces if not fully closed.

## Summary of which pieces are checkable now

```text
Checkable algebra/group wrappers:
  tateToShortVC and coefficient equality to `shortW(-27c4,-54c6)`
  C10 specialization if A10/B10 match local standard invariants
  Delta10 nonzero from Tate discriminant plus denominator clearing
  translate order-10 point to origin
  origin a3 ≠ 0 from exact order 10
  kill a4 and preserve a6/order
  scale to Tate form after a2≠0

Genuine elliptic-curve normal-form residual:
  OriginOrderDividesThreeWhenA2A4A6ZeroStatement

Potential local-definition residual only:
  If A10/B10 are not exactly `-27*c4/-54*c6` after C10 substitution, determine the final short scaling and add it as an explicit variable change rather than hiding it in `kubert_C10_square`.
```
