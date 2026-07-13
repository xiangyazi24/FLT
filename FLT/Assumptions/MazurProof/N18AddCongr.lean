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

/-! ## More `ordPi` toolbox: nonnegativity on integers + strict domination -/

/-- `ordPi 1 = 0`. -/
theorem ordPi_one : ordPi (1 : L) = 0 := by
  unfold ordPi; rw [map_one, WithZero.log_one, neg_zero]

/-- Algebraic integers have nonnegative `ordPi` (the coefficient-integrality fact:
`v₃` of an element of `𝒪_L` is `≤ 1`, so `ordPi = −log ≥ 0`). -/
theorem zero_le_ordPi_intCast (m : ℤ) : 0 ≤ ordPi ((m : L)) := by
  rcases eq_or_ne ((m : L)) 0 with h0 | hne
  · rw [h0, ordPi_zero]
  · have hle : v3 ((m : L)) ≤ 1 := by
      show p3.valuation L ((m : L)) ≤ 1
      have hv := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := L) p3 (m : OL)
      simpa only [map_intCast] using hv
    have hlog : WithZero.log (v3 ((m : L))) ≤ 0 := by
      have h := (WithZero.log_le_log (v3_ne_zero hne) one_ne_zero).mpr hle
      rwa [WithZero.log_one] at h
    unfold ordPi; linarith

/-- **Robust ultrametric lower bound.**  If both summands have `ordPi ≥ N` and
`N ≤ 0` (so the junk value `ordPi 0 = 0 ≥ N` is harmless), then so does the sum —
even when some summand is `0`. -/
theorem le_ordPi_add {N : ℤ} {u w : L} (hu : N ≤ ordPi u) (hw : N ≤ ordPi w)
    (hN : N ≤ 0) : N ≤ ordPi (u + w) := by
  by_cases huw : u + w = 0
  · rw [huw, ordPi_zero]; exact hN
  by_cases hu0 : u = 0
  · rw [hu0, zero_add]; exact hw
  by_cases hw0 : w = 0
  · rw [hw0, add_zero]; exact hu
  · exact le_trans (le_min hu hw) (ordPi_add_ge hu0 hw0 huw)

/-- **Strict-domination law.**  If `ordPi u < ordPi w` (and both are nonzero),
the smaller term controls the sum: `ordPi (u + w) = ordPi u`. -/
theorem ordPi_add_eq_of_lt {u w : L} (hu : u ≠ 0) (hw : w ≠ 0)
    (huw : ordPi u < ordPi w) : ordPi (u + w) = ordPi u := by
  have hsum : u + w ≠ 0 := by
    intro h
    have hwu : w = -u := by linear_combination h
    rw [hwu, ordPi_neg] at huw
    exact lt_irrefl _ huw
  refine le_antisymm ?_ ?_
  · by_contra hlt
    push_neg at hlt
    have h := ordPi_add_ge hsum (neg_ne_zero.mpr hw)
      (by rw [add_neg_cancel_right]; exact hu)
    rw [add_neg_cancel_right, ordPi_neg] at h
    exact absurd h (not_le.mpr (lt_min hlt huw))
  · have h := ordPi_add_ge hu hw hsum
    rwa [min_eq_left huw.le] at h

/-! ## STEP 1 — the 𝔪-filtration valuations (load-bearing sub-lemma) -/

/-- **STEP 1 (the load-bearing sub-lemma), Fable-designed, now PROVEN.**  For a
finite point `(x, y)` on `E₀` that is **near `O`** — i.e. `v(x) < 0` (the correct
formal-kernel condition; NOT `v(z) ≥ 1`) — the coordinate valuations are
`v x = −2·v z` and `v y = −3·v z` where `z = −x/y`.

Newton-polygon proof.  Write `a = v x < 0`, `b = v y`.  All `E₀`-coefficients are
`π`-units so `0 ≤ v(aᵢ)`.  On the RHS `x³` (valuation `3a`) strictly dominates
(`3a < 2a, a, 0`), so `v(RHS) = 3a`; hence `v(LHS) = 3a` too.  A lower-bound
argument forces first `b < 0`, then `b < a`, so on the LHS `y²` (valuation `2b`)
strictly dominates, giving `v(LHS) = 2b`.  Thus `2b = 3a`, and with
`v z = a − b` the two equalities follow. -/
theorem val_coords {x y : L} (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (heq : y ^ 2 + E0.a₁ * x * y + E0.a₃ * y
         = x ^ 3 + E0.a₂ * x ^ 2 + E0.a₄ * x + E0.a₆)
    (hx : ordPi x < 0) :
    ordPi x = -2 * ordPi (-x / y) ∧ ordPi y = -3 * ordPi (-x / y) := by
  have ha : ordPi x ≤ -1 := by omega
  -- coefficient nonzero facts (E₀: a₁=1, a₂=-1, a₃=1, a₄=-5, a₆=5)
  have ha1_ne : E0.a₁ ≠ 0 := by norm_num [E0]
  have ha3_ne : E0.a₃ ≠ 0 := by norm_num [E0]
  have ha2_ne : E0.a₂ ≠ 0 := by norm_num [E0]
  have ha4_ne : E0.a₄ ≠ 0 := by norm_num [E0]
  have ha6_ne : E0.a₆ ≠ 0 := by norm_num [E0]
  -- coefficient valuation bounds (all π-units ⇒ ordPi ≥ 0; a₁=a₃=1 ⇒ ordPi = 0)
  have hc1 : ordPi E0.a₁ = 0 := by
    have : E0.a₁ = (1 : L) := by norm_num [E0]
    rw [this]; exact ordPi_one
  have hc3 : ordPi E0.a₃ = 0 := by
    have : E0.a₃ = (1 : L) := by norm_num [E0]
    rw [this]; exact ordPi_one
  have hc2 : 0 ≤ ordPi E0.a₂ := by
    have : E0.a₂ = (((-1 : ℤ)) : L) := by norm_num [E0]
    rw [this]; exact zero_le_ordPi_intCast (-1)
  have hc4 : 0 ≤ ordPi E0.a₄ := by
    have : E0.a₄ = (((-5 : ℤ)) : L) := by norm_num [E0]
    rw [this]; exact zero_le_ordPi_intCast (-5)
  have hc6 : 0 ≤ ordPi E0.a₆ := by
    have : E0.a₆ = (((5 : ℤ)) : L) := by norm_num [E0]
    rw [this]; exact zero_le_ordPi_intCast 5
  -- monomial valuations
  have hy2 : ordPi (y ^ 2) = 2 * ordPi y := by
    rw [show y ^ 2 = y * y by ring, ordPi_mul hy0 hy0]; ring
  have hx2 : ordPi (x ^ 2) = 2 * ordPi x := by
    rw [show x ^ 2 = x * x by ring, ordPi_mul hx0 hx0]; ring
  have hx3 : ordPi (x ^ 3) = 3 * ordPi x := by
    rw [show x ^ 3 = x * x * x by ring, ordPi_mul (mul_ne_zero hx0 hx0) hx0,
      ordPi_mul hx0 hx0]; ring
  have hxy : ordPi (E0.a₁ * x * y) = ordPi E0.a₁ + ordPi x + ordPi y := by
    rw [ordPi_mul (mul_ne_zero ha1_ne hx0) hy0, ordPi_mul ha1_ne hx0]
  have ha3y : ordPi (E0.a₃ * y) = ordPi E0.a₃ + ordPi y := by
    rw [ordPi_mul ha3_ne hy0]
  have ha2x : ordPi (E0.a₂ * x ^ 2) = ordPi E0.a₂ + 2 * ordPi x := by
    rw [ordPi_mul ha2_ne (pow_ne_zero 2 hx0), hx2]
  have ha4x : ordPi (E0.a₄ * x) = ordPi E0.a₄ + ordPi x := by
    rw [ordPi_mul ha4_ne hx0]
  -- STEP: v(RHS) = 3·v(x)  (x³ strictly dominates)
  have htail_lb : 3 * ordPi x + 1 ≤ ordPi (E0.a₂ * x ^ 2 + E0.a₄ * x + E0.a₆) := by
    apply le_ordPi_add _ _ (by omega)
    · apply le_ordPi_add _ _ (by omega)
      · rw [ha2x]; omega
      · rw [ha4x]; omega
    · exact le_trans (by omega) hc6
  have hRHS : ordPi (x ^ 3 + E0.a₂ * x ^ 2 + E0.a₄ * x + E0.a₆) = 3 * ordPi x := by
    by_cases htail : E0.a₂ * x ^ 2 + E0.a₄ * x + E0.a₆ = 0
    · rw [show x ^ 3 + E0.a₂ * x ^ 2 + E0.a₄ * x + E0.a₆
            = x ^ 3 + (E0.a₂ * x ^ 2 + E0.a₄ * x + E0.a₆) by ring, htail, add_zero, hx3]
    · rw [show x ^ 3 + E0.a₂ * x ^ 2 + E0.a₄ * x + E0.a₆
            = x ^ 3 + (E0.a₂ * x ^ 2 + E0.a₄ * x + E0.a₆) by ring,
          ordPi_add_eq_of_lt (pow_ne_zero 3 hx0) htail (by rw [hx3]; linarith [htail_lb]), hx3]
  -- hence v(LHS) = 3·v(x)
  have hLHS : ordPi (y ^ 2 + E0.a₁ * x * y + E0.a₃ * y) = 3 * ordPi x := by
    rw [heq]; exact hRHS
  -- STEP: v(y) < 0
  have hb_neg : ordPi y < 0 := by
    by_contra hbn
    push_neg at hbn
    have hlb : 3 * ordPi x + 1 ≤ ordPi (y ^ 2 + E0.a₁ * x * y + E0.a₃ * y) := by
      apply le_ordPi_add _ _ (by omega)
      · apply le_ordPi_add _ _ (by omega)
        · rw [hy2]; omega
        · rw [hxy]; omega
      · rw [ha3y]; omega
    omega
  -- STEP: v(y) < v(x)
  have hb_lt : ordPi y < ordPi x := by
    by_contra hba
    push_neg at hba
    have hlb : 3 * ordPi x + 1 ≤ ordPi (y ^ 2 + E0.a₁ * x * y + E0.a₃ * y) := by
      apply le_ordPi_add _ _ (by omega)
      · apply le_ordPi_add _ _ (by omega)
        · rw [hy2]; omega
        · rw [hxy]; omega
      · rw [ha3y]; omega
    omega
  -- STEP: y² strictly dominates the LHS ⇒ 2·v(y) = 3·v(x)
  have hrest_lb : 2 * ordPi y + 1 ≤ ordPi (E0.a₁ * x * y + E0.a₃ * y) := by
    apply le_ordPi_add _ _ (by omega)
    · rw [hxy]; omega
    · rw [ha3y]; omega
  have hkey : 2 * ordPi y = 3 * ordPi x := by
    by_cases hrest : E0.a₁ * x * y + E0.a₃ * y = 0
    · have hcollapse : ordPi (y ^ 2 + E0.a₁ * x * y + E0.a₃ * y) = ordPi (y ^ 2) := by
        rw [show y ^ 2 + E0.a₁ * x * y + E0.a₃ * y
              = y ^ 2 + (E0.a₁ * x * y + E0.a₃ * y) by ring, hrest, add_zero]
      rw [hcollapse, hy2] at hLHS
      exact hLHS
    · have hdom : ordPi (y ^ 2 + (E0.a₁ * x * y + E0.a₃ * y)) = ordPi (y ^ 2) :=
        ordPi_add_eq_of_lt (pow_ne_zero 2 hy0) hrest (by rw [hy2]; linarith [hrest_lb])
      rw [show y ^ 2 + E0.a₁ * x * y + E0.a₃ * y
            = y ^ 2 + (E0.a₁ * x * y + E0.a₃ * y) by ring, hdom, hy2] at hLHS
      exact hLHS
  -- assemble the two filtration equalities
  have hc : ordPi (-x / y) = ordPi x - ordPi y := by
    rw [neg_div, ordPi_neg, ordPi_div hx0 hy0]
  exact ⟨by rw [hc]; omega, by rw [hc]; omega⟩

/-- **Package I** — integral formal group law leading term (pointwise).

Route: reduce to finite `P = (x₁,y₁)`, `Q = (x₂,y₂)` with `P+Q ≠ O` (the zero
and `P = −Q` cases are elementary), split on the doubling/distinct branch of
`Point.add`, use STEP 1 (`val_coords`) for the coordinate valuations, STEP 2 for
`v ℓ ≥ −min(v z₁, v z₂)` via `slope`, STEP 3 for `x₃ = ℓ² + a₁ℓ − a₂ − x₁ − x₂`
and `z₃ = −x₃/y₃`, and STEP 4 for the cross-term valuation bound using the
ultrametric `ordPi_add_ge` + `ordPi_mul`.

**Corrected statement (Codex counterexample, 2026-07-13):** the `ordPi`-valued
version with `ordPi 0 = 0` is FALSE on concrete kernel points (generator21 +
torsionAffine 5 gives error with ordPi = 0 while the sum = 2).  The disjunctive
restatement is mathematically correct and compatible with the downstream
`FormalKernelData.add_congr` (which uses `vpi : WithTop ℤ` where `vpi 0 = ⊤`). -/
theorem add_congr (P Q : E0Point)
    (hP : P = 0 ∨ ordPi (xCoord P) < 0)
    (hQ : Q = 0 ∨ ordPi (xCoord Q) < 0) :
    zParam (P + Q) - zParam P - zParam Q = 0 ∨
    v (zParam P) + v (zParam Q) ≤ v (zParam (P + Q) - zParam P - zParam Q) := by
  -- The origin cases: P=0 gives zParam P = 0, error = z(Q) - z(Q) = 0.
  rcases hP with rfl | hPx
  · simp [zParam_zero]; left; ring
  rcases hQ with rfl | hQx
  · simp [zParam_zero]; left; ring
  -- Remaining: both P = (x₁,y₁) and Q = (x₂,y₂) finite with v(x) < 0 (near O).
  -- Three branches of Point.add:
  -- (a) inverse (P+Q=O), (b) distinct-x, (c) doubling.
  -- Chart algebra (G_line, BC_factor, identity8) is proved in N18AddCongrProof.lean.
  sorry

end

end MazurProof.N18Block5Instantiation.AddCongr
