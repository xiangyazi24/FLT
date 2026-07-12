import FLT.Assumptions.MazurProof.N18RouteC_Isogeny
import FLT.Assumptions.MazurProof.N18RouteC_ThreeAdic

/-!
# Package I — the formal-group **addition congruence** for `E₀`, pointwise

For `E₀ = 162.c3` over `L = ℚ(ζ₉)⁺`, the formal parameter `z(P) = −x(P)/y(P)`
(with `z(O)=0`) and the π-adic additive valuation `v = ThreeAdic.ordPi`
(`v(π)=1`, `v(3)=3`), we prove the leading-order integrality of the elliptic
formal group law **pointwise** (no formal power series type):

`add_congr : v(zP) ≥ 1 → v(zQ) ≥ 1 → v(zP) + v(zQ) ≤ v(z(P⊕Q) − zP − zQ)`.

The proof route (Fable's Deliverable 4) works on the affine chart near `O`:
* **STEP 1** (`val_x`, `val_y`) — the 𝔪-filtration valuations: for a finite
  point near `O`, `v(x) = −2·v(z)`, `v(y) = −3·v(z)`.  Derived from `z = −x/y`
  and the Weierstrass relation via a Newton-polygon argument.  **This is the
  load-bearing sub-lemma.**
* **STEP 2** — slope valuation bound `v(ℓ) ≥ −min(v z₁, v z₂)`.
* **STEP 3** — `x₃ = ℓ² + a₁ℓ − a₂ − x₁ − x₂`; expand ⇒ `z₃ = z₁ + z₂ + …`.
* **STEP 4** — `z₃ − z₁ − z₂` = cross terms, each monomial carrying a factor
  from *each* of `z₁, z₂` (because `F(X,0)=X`) ⇒ `v ≥ v z₁ + v z₂`.

This file discharges **Package I** (`FormalKernelData.add_congr`) of the N18
Block-5 instantiation.  Match `zParam`/`v` to `N18Block5Instantiation.lean`.
-/

open scoped Classical
open scoped WeierstrassCurve.Affine

namespace MazurProof.N18Block5Instantiation.AddCongr

open MazurProof.N18RouteC
open MazurProof.N18RouteC.Isogeny
open MazurProof.N18RouteC.ThreeAdic
open WeierstrassCurve

noncomputable section

/-- Formal parameter `z = −x/y` of a point of `E₀(L)` (`z(O) = 0`). -/
def zParam : E0Point → L
  | .zero => 0
  | .some x y _ => -x / y

@[simp] theorem zParam_zero : zParam (0 : E0Point) = 0 := rfl

@[simp] theorem zParam_some (x y : L) (h : WeierstrassCurve.Affine.Nonsingular E0 x y) :
    zParam (.some x y h) = -x / y := rfl

/-- The π-adic additive valuation used by the formal-kernel filtration
(`v(π) = 1`, `v(3) = 3`). -/
abbrev v : L → ℤ := ordPi

/-! ## `ordPi` valuation toolbox (verified)

`ordPi x = −log (v3 x)` where `v3 : Valuation L ℤₘ₀` is the height-one π-adic
valuation.  These are the additive-valuation laws the formal-group estimate
needs, and are proven here from `Valuation.map_mul` / `map_add` + `WithZero.log`.
-/

theorem v3_ne_zero {x : L} (hx : x ≠ 0) : v3 x ≠ 0 :=
  v3.ne_zero_iff.mpr hx

/-- `ordPi` is additive on products of nonzero elements. -/
theorem ordPi_mul {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) :
    ordPi (a * b) = ordPi a + ordPi b := by
  unfold ordPi
  rw [map_mul, WithZero.log_mul (v3_ne_zero ha) (v3_ne_zero hb)]
  ring

/-- `ordPi (a/b) = ordPi a − ordPi b`. -/
theorem ordPi_div {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) :
    ordPi (a / b) = ordPi a - ordPi b := by
  unfold ordPi
  rw [map_div₀, WithZero.log_div (v3_ne_zero ha) (v3_ne_zero hb)]
  ring

@[simp] theorem ordPi_neg (a : L) : ordPi (-a) = ordPi a := by
  unfold ordPi; rw [Valuation.map_neg]

@[simp] theorem ordPi_zero : ordPi (0 : L) = 0 := by
  unfold ordPi; rw [map_zero, WithZero.log_zero, neg_zero]

/-- Ultrametric law: `ordPi (a+b) ≥ min (ordPi a) (ordPi b)`. -/
theorem ordPi_add_ge {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) :
    min (ordPi a) (ordPi b) ≤ ordPi (a + b) := by
  have hmax : v3 (a + b) ≤ max (v3 a) (v3 b) := v3.map_add a b
  have key : WithZero.log (v3 (a + b)) ≤
      max (WithZero.log (v3 a)) (WithZero.log (v3 b)) := by
    rcases le_total (v3 a) (v3 b) with h | h
    · have hle : v3 (a + b) ≤ v3 b := le_trans hmax (by rw [max_eq_right h])
      exact le_trans ((WithZero.log_le_log (v3_ne_zero hab) (v3_ne_zero hb)).mpr hle)
        (le_max_right _ _)
    · have hle : v3 (a + b) ≤ v3 a := le_trans hmax (by rw [max_eq_left h])
      exact le_trans ((WithZero.log_le_log (v3_ne_zero hab) (v3_ne_zero ha)).mpr hle)
        (le_max_left _ _)
  unfold ordPi
  omega

/-! ## STEP 1 — the 𝔪-filtration valuations (load-bearing sub-lemma) -/

/-- **STEP 1 (the load-bearing sub-lemma).**  For a finite point `(x, y)` near
`O` — i.e. `z = −x/y` lies in the formal kernel, `v z ≥ 1` — the coordinate
valuations are `v x = −2·v z` and `v y = −3·v z`.

This is the 𝔪-filtration statement, derived from `z = −x/y`, `w = −1/y`, and the
Weierstrass relation `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` by a Newton-polygon
argument on `(v x, v y)`:  writing `a = v x`, `b = v y`, the dominant terms of
the two sides are `y²` (valuation `2b`) and `x³` (valuation `3a`), so `2b = 3a`;
together with `v z = a − b ≥ 1` this forces `a = −2·v z`, `b = −3·v z`.

**Not yet proven** — this is the remaining `sorry`; see the report. -/
theorem val_coords {x y : L} (h : WeierstrassCurve.Affine.Nonsingular E0 x y)
    (hz : 1 ≤ ordPi (-x / y)) :
    ordPi x = -2 * ordPi (-x / y) ∧ ordPi y = -3 * ordPi (-x / y) := by
  sorry

/-- **Package I** — integral formal group law leading term (pointwise).

Route: reduce to finite `P = (x₁,y₁)`, `Q = (x₂,y₂)` with `P+Q ≠ O` (the zero
and `P = −Q` cases are elementary), split on the doubling/distinct branch of
`Point.add`, use STEP 1 (`val_coords`) for the coordinate valuations, STEP 2 for
`v ℓ ≥ −min(v z₁, v z₂)` via `slope`, STEP 3 for `x₃ = ℓ² + a₁ℓ − a₂ − x₁ − x₂`
and `z₃ = −x₃/y₃`, and STEP 4 for the cross-term valuation bound using the
ultrametric `ordPi_add_ge` + `ordPi_mul`.

**Not yet fully wired** — currently a `sorry`; see the report for the exact
remaining reduction (STEP 2–4 on top of STEP 1). -/
theorem add_congr (P Q : E0Point)
    (hP : 1 ≤ v (zParam P)) (hQ : 1 ≤ v (zParam Q)) :
    v (zParam P) + v (zParam Q) ≤ v (zParam (P + Q) - zParam P - zParam Q) := by
  -- The origin cases are vacuous: `v (zParam 0) = 0` contradicts `hP`/`hQ`.
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · change 1 ≤ ordPi (0 : L) at hP
    rw [ordPi_zero] at hP; exact absurd hP (by norm_num)
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · change 1 ≤ ordPi (0 : L) at hQ
    rw [ordPi_zero] at hQ; exact absurd hQ (by norm_num)
  -- Remaining: both `P = (x₁,y₁)` and `Q = (x₂,y₂)` finite.  STEP 2–4 on top of
  -- STEP 1 (`val_coords`), splitting on the doubling/distinct branch of
  -- `Point.add`.  **Remaining reduction — see report.**
  sorry

end

end MazurProof.N18Block5Instantiation.AddCongr
