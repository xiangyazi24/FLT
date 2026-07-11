import FLT.Assumptions.MazurProof.CyclicExclusion21

/-!
# An explicit affine model for the order-21 obstruction

The first half of the order-21 argument produces rational numbers `b,c,X,Y`
with

* `b != 0`;
* `c^3 - b^2 + b*c = 0` (the marked Tate point has order seven);
* `(X,Y)` lies on the Tate curve;
* the third division polynomial vanishes at `X`.

This file removes the redundant Tate parameters and the `Y` coordinate.
Every nondegenerate solution of the order-seven equation is uniquely of the
form

`c = t(t-1)`, `b = t^2(t-1)`, with `t != 0,1`.

Completing the square in the Tate equation then gives the explicit
one-dimensional affine model

`G21(t,X) = 0`, `Z^2 = D21(t,X)`.

Thus the remaining order-21 arithmetic problem is stated entirely in terms of
two explicit integer polynomials.  No elliptic-curve group law or division
polynomial remains in the final equivalence.
-/

namespace MazurProof.RationalPointsN21

noncomputable section

open CyclicExclusion21

/-! ## The order-seven Tate parametrization -/

/-- Kubert's `c` parameter for a marked point of order seven. -/
def kubertC7 (t : ℚ) : ℚ := t * (t - 1)

/-- Kubert's `b` parameter for a marked point of order seven. -/
def kubertB7 (t : ℚ) : ℚ := t ^ 2 * (t - 1)

theorem kubert_F7 (t : ℚ) :
    F7 (kubertB7 t) (kubertC7 t) = 0 := by
  simp only [F7, kubertB7, kubertC7]
  ring

theorem c_ne_zero_of_F7
    {b c : ℚ} (hb : b ≠ 0) (hF7 : F7 b c = 0) : c ≠ 0 := by
  intro hc
  subst c
  simp only [F7] at hF7
  apply hb
  nlinarith [sq_nonneg b]

/-- The parameter recovered from a nondegenerate order-seven Tate solution. -/
def recoveredT (b c : ℚ) : ℚ := b / c

theorem recovered_c
    {b c : ℚ} (hb : b ≠ 0) (hF7 : F7 b c = 0) :
    c = kubertC7 (recoveredT b c) := by
  have hc := c_ne_zero_of_F7 hb hF7
  simp only [recoveredT, kubertC7]
  simp only [F7] at hF7
  field_simp [hc] <;> nlinarith [hF7]

theorem recovered_b
    {b c : ℚ} (hb : b ≠ 0) (hF7 : F7 b c = 0) :
    b = kubertB7 (recoveredT b c) := by
  have hc := c_ne_zero_of_F7 hb hF7
  have hcparam := recovered_c hb hF7
  calc
    b = recoveredT b c * c := by
      simpa only [recoveredT] using (div_mul_cancel₀ b hc).symm
    _ = recoveredT b c * kubertC7 (recoveredT b c) := by rw [← hcparam]
    _ = kubertB7 (recoveredT b c) := by
      simp only [kubertB7, kubertC7]
      ring

theorem recoveredT_ne_zero
    {b c : ℚ} (hb : b ≠ 0) (hF7 : F7 b c = 0) :
    recoveredT b c ≠ 0 := by
  exact div_ne_zero hb (c_ne_zero_of_F7 hb hF7)

theorem recoveredT_ne_one
    {b c : ℚ} (hb : b ≠ 0) (hF7 : F7 b c = 0) :
    recoveredT b c ≠ 1 := by
  have hc := c_ne_zero_of_F7 hb hF7
  intro ht
  have hbc : b = c := by
    apply (div_eq_one_iff_eq hc).mp
    exact ht
  rw [hbc] at hF7
  simp only [F7] at hF7
  ring_nf at hF7
  exact (pow_ne_zero 3 hc) hF7

theorem F7_parametrization
    {b c : ℚ} (hb : b ≠ 0) (hF7 : F7 b c = 0) :
    ∃ t : ℚ, t ≠ 0 ∧ t ≠ 1 ∧
      b = kubertB7 t ∧ c = kubertC7 t := by
  exact ⟨recoveredT b c, recoveredT_ne_zero hb hF7,
    recoveredT_ne_one hb hF7, recovered_b hb hF7, recovered_c hb hF7⟩

theorem kubertB7_ne_zero {t : ℚ} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    kubertB7 t ≠ 0 := by
  exact mul_ne_zero (pow_ne_zero 2 ht0) (sub_ne_zero.mpr ht1)

/-! ## The explicit order-21 model -/

/-- The third-division equation after substituting the order-seven family. -/
def G21 (t X : ℚ) : ℚ :=
  3 * X ^ 4
    + (t ^ 4 - 6 * t ^ 3 + 3 * t ^ 2 + 2 * t + 1) * X ^ 3
    + (3 * t ^ 5 - 6 * t ^ 4 + 3 * t ^ 2) * X ^ 2
    + (3 * t ^ 6 - 6 * t ^ 5 + 3 * t ^ 4) * X
    - t ^ 9 + 3 * t ^ 8 - 3 * t ^ 7 + t ^ 6

/-- The square obtained by completing the square in the Tate equation. -/
def D21 (t X : ℚ) : ℚ :=
  4 * X ^ 3
    + (t ^ 4 - 6 * t ^ 3 + 3 * t ^ 2 + 2 * t + 1) * X ^ 2
    + (2 * t ^ 5 - 4 * t ^ 4 + 2 * t ^ 2) * X
    + t ^ 6 - 2 * t ^ 5 + t ^ 4

/-- The completed-square coordinate attached to a Tate point. -/
def completedY (t X Y : ℚ) : ℚ :=
  2 * Y + (1 - kubertC7 t) * X - kubertB7 t

theorem Psi3X_kubert_eq_G21 (t X : ℚ) :
    Psi3X (kubertB7 t) (kubertC7 t) X = G21 t X := by
  simp only [Psi3X, kubertB7, kubertC7, G21]
  ring

/-- Completing the square is exactly four times the Tate equation residual. -/
theorem completedY_sq_sub_D21 (t X Y : ℚ) :
    completedY t X Y ^ 2 - D21 t X =
      4 * (Y ^ 2 + (1 - kubertC7 t) * X * Y - kubertB7 t * Y
        - (X ^ 3 - kubertB7 t * X ^ 2)) := by
  simp only [completedY, D21, kubertB7, kubertC7]
  ring

theorem TateEq_kubert_iff_completed_square (t X Y : ℚ) :
    TateEq (kubertB7 t) (kubertC7 t) X Y ↔
      completedY t X Y ^ 2 = D21 t X := by
  rw [show TateEq (kubertB7 t) (kubertC7 t) X Y ↔
      Y ^ 2 + (1 - kubertC7 t) * X * Y - kubertB7 t * Y
        - (X ^ 3 - kubertB7 t * X ^ 2) = 0 by
    simp only [TateEq]
    constructor <;> intro h <;> linarith]
  have h := completedY_sq_sub_D21 t X Y
  constructor <;> intro hz
  · apply sub_eq_zero.mp
    rw [h, hz, mul_zero]
  · have hzero : completedY t X Y ^ 2 - D21 t X = 0 :=
      sub_eq_zero.mpr hz
    rw [h] at hzero
    nlinarith

/-- Recover the original `Y` coordinate from a square root of `D21`. -/
def recoveredY (t X Z : ℚ) : ℚ :=
  (Z - (1 - kubertC7 t) * X + kubertB7 t) / 2

theorem completedY_recoveredY (t X Z : ℚ) :
    completedY t X (recoveredY t X Z) = Z := by
  simp only [completedY, recoveredY]
  ring

theorem TateEq_recoveredY_of_square
    {t X Z : ℚ} (hD : Z ^ 2 = D21 t X) :
    TateEq (kubertB7 t) (kubertC7 t) X (recoveredY t X Z) := by
  rw [TateEq_kubert_iff_completed_square, completedY_recoveredY]
  exact hD

/-! ## Exact equivalence with the original obstruction -/

/-- The explicit noncuspidal affine model left by the order-21 reduction. -/
def ExplicitObstruction21 : Prop :=
  ∃ t X Z : ℚ, t ≠ 0 ∧ t ≠ 1 ∧ G21 t X = 0 ∧ Z ^ 2 = D21 t X

theorem obstruction_to_explicit
    {b c X Y : ℚ} (hobs : Obstruction21 b c X Y) :
    ExplicitObstruction21 := by
  rcases hobs with ⟨hb, hF7, hTate, hPsi⟩
  obtain ⟨t, ht0, ht1, hbparam, hcparam⟩ := F7_parametrization hb hF7
  subst b
  subst c
  refine ⟨t, X, completedY t X Y, ht0, ht1, ?_, ?_⟩
  · rw [← Psi3X_kubert_eq_G21]
    exact hPsi
  · exact (TateEq_kubert_iff_completed_square t X Y).mp hTate

theorem explicit_to_obstruction
    (hobs : ExplicitObstruction21) :
    ∃ b c X Y : ℚ, Obstruction21 b c X Y := by
  rcases hobs with ⟨t, X, Z, ht0, ht1, hG, hD⟩
  refine ⟨kubertB7 t, kubertC7 t, X, recoveredY t X Z,
    kubertB7_ne_zero ht0 ht1, kubert_F7 t,
    TateEq_recoveredY_of_square hD, ?_⟩
  rw [Psi3X_kubert_eq_G21]
  exact hG

theorem obstruction_iff_explicit :
    (∃ b c X Y : ℚ, Obstruction21 b c X Y) ↔ ExplicitObstruction21 := by
  constructor
  · rintro ⟨b, c, X, Y, hobs⟩
    exact obstruction_to_explicit hobs
  · exact explicit_to_obstruction

end

end MazurProof.RationalPointsN21
