import FLT.Assumptions.MazurProof.CyclicOrderReduction

/-!
# Cyclic order 15 exclusion

A rational point of exact order `15 = 3 * 5` gives rational points of
orders `5` and `3` by taking `3 • P` and `5 • P`.  The remaining arithmetic
input is the rational-points computation on `X₁(15)`: over `ℚ`, the curve has
only cuspidal rational points, equivalently no elliptic curve over `ℚ` has
simultaneously a rational point of order `3` and one of order `5`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

/-! ## Elementary order extraction from a point of order 15 -/

theorem addOrderOf_three_nsmul_of_order15
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {P : (E⁄ℚ).Point} (hP : addOrderOf P = 15) :
    addOrderOf (3 • P) = 5 := by
  rw [addOrderOf_nsmul' P (by norm_num : (3 : ℕ) ≠ 0), hP]
  norm_num

theorem addOrderOf_five_nsmul_of_order15
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {P : (E⁄ℚ).Point} (hP : addOrderOf P = 15) :
    addOrderOf (5 • P) = 3 := by
  rw [addOrderOf_nsmul' P (by norm_num : (5 : ℕ) ≠ 0), hP]
  norm_num

theorem order15_gives_order5
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hord : HasRationalPointOfOrder E 15) :
    HasRationalPointOfOrder E 5 := by
  rcases hord with ⟨P, hP⟩
  exact ⟨3 • P, addOrderOf_three_nsmul_of_order15 hP⟩

theorem order15_gives_order3
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hord : HasRationalPointOfOrder E 15) :
    HasRationalPointOfOrder E 3 := by
  rcases hord with ⟨P, hP⟩
  exact ⟨5 • P, addOrderOf_five_nsmul_of_order15 hP⟩

theorem order15_gives_orders3_and5
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hord : HasRationalPointOfOrder E 15) :
    HasRationalPointOfOrder E 3 ∧ HasRationalPointOfOrder E 5 :=
  ⟨order15_gives_order3 E hord, order15_gives_order5 E hord⟩

/-! ## Position of `15` in the composite-order reduction framework -/

theorem needs_composite_exclusion_15 : NeedsCompositeExclusion 15 := by
  refine needs_composite_exclusion_of_small_prime_factors ?_ ?_ ?_
  · norm_num
  · norm_num [allowedCyclicOrders]
  · intro p hp hpdvd
    have hp35 : p ∣ 3 * 5 := by
      simpa using hpdvd
    rcases (Nat.Prime.dvd_mul hp).mp hp35 with hp3 | hp5
    · have hp_eq : p = 3 :=
        (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp3
      rw [hp_eq]
      norm_num [allowedPrimeOrders]
    · have hp_eq : p = 5 :=
        (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp5
      rw [hp_eq]
      norm_num [allowedPrimeOrders]

theorem no_order15_from_future_composite_exclusions
    (hcomp : FutureCompositeExclusions)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 15 :=
  hcomp E (n := 15) (by norm_num) needs_composite_exclusion_15

namespace CyclicExclusion15

/-! ## Tate normal form for the `3`-and-`5` obstruction -/

/--
The Tate normal form after imposing that `(0,0)` has order `5`:

`y² + (1-b)xy - by = x³ - bx²`.

For the usual two-parameter Tate normal form, the order-`5` condition is
`c = b`.
-/
def tateOrder5Curve (b : ℚ) : WeierstrassCurve ℚ where
  a₁ := 1 - b
  a₂ := -b
  a₃ := -b
  a₄ := 0
  a₆ := 0

/-- The explicit `ψ₃` polynomial in the Tate order-`5` parameter. -/
def tateOrder5Psi3 (b x : ℚ) : ℚ :=
  3 * x ^ 4 + (b ^ 2 - 6 * b + 1) * x ^ 3 +
    3 * (b ^ 2 - b) * x ^ 2 + 3 * b ^ 2 * x - b ^ 3

/-- The nonsingularity condition for the Tate order-`5` normal form. -/
def TateOrder5NonsingularParameter (b : ℚ) : Prop :=
  b ^ 5 * (b ^ 2 - 11 * b - 1) ≠ 0

/--
The exact Diophantine obstruction needed for `X₁(15)`: a nonsingular Tate
order-`5` normal form has no rational `x`-coordinate satisfying `ψ₃(x)=0`.
-/
def TateOrder5Psi3RootSolution (b x : ℚ) : Prop :=
  TateOrder5NonsingularParameter b ∧ tateOrder5Psi3 b x = 0

theorem tateOrder5Curve_discriminant (b : ℚ) :
    (tateOrder5Curve b).Δ = b ^ 5 * (b ^ 2 - 11 * b - 1) := by
  simp [tateOrder5Curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem tateOrder5Curve_psi3_eval (b x : ℚ) :
    ((tateOrder5Curve b).Ψ₃).eval x = tateOrder5Psi3 b x := by
  simp [tateOrder5Curve, tateOrder5Psi3, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

/--
Moduli and division-polynomial bridge for `X₁(15)`.

From a curve over `ℚ` with rational points of exact orders `3` and `5`, put
the order-`5` point in Tate normal form, use the order-`5` condition `c = b`,
and evaluate the third division polynomial at the rational `x`-coordinate of
the order-`3` point.
-/
def SimultaneousOrder3And5TateBridge : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
    HasRationalPointOfOrder E 3 ∧ HasRationalPointOfOrder E 5 →
      ∃ b x : ℚ, TateOrder5Psi3RootSolution b x

/--
Residual bridge from the current torsion predicate to the explicit Tate
normal-form Diophantine problem.
-/
theorem simultaneous_order3_and5_tate_bridge :
    SimultaneousOrder3And5TateBridge := by
  intro E hEll htors
  sorry

/--
Final Diophantine input.

Explicitly, there are no `b x : ℚ` such that

`b^5 * (b^2 - 11*b - 1) ≠ 0`

and

`3*x^4 + (b^2 - 6*b + 1)*x^3 + 3*(b^2-b)*x^2 + 3*b^2*x - b^3 = 0`.

This is the rational-points computation on `X₁(15)` in Tate-normal-form
coordinates; the rational points are cusps, and the nonsingularity condition
excludes them.
-/
theorem no_tate_order5_psi3_root_solution :
    ¬ ∃ b x : ℚ, TateOrder5Psi3RootSolution b x := by
  sorry

end CyclicExclusion15

/-! ## The remaining `X₁(15)` arithmetic input -/

/--
The `X₁(15)` rational-points input.

Mathematically, `X₁(15)` is an elliptic curve of rank `0` over `ℚ`; its
rational points are cusps.  In the present torsion language this says that no
elliptic curve over `ℚ` has both a rational point of order `3` and a rational
point of order `5`.
-/
theorem x1_15_no_simultaneous_rational_3_and_5_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ (HasRationalPointOfOrder E 3 ∧ HasRationalPointOfOrder E 5) := by
  intro htors
  obtain ⟨b, x, hbx⟩ :=
    CyclicExclusion15.simultaneous_order3_and5_tate_bridge E htors
  exact CyclicExclusion15.no_tate_order5_psi3_root_solution ⟨b, x, hbx⟩

/-- No elliptic curve over `ℚ` has a rational point of exact order `15`. -/
theorem no_rational_point_of_order_15
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 15 := by
  intro hord
  exact x1_15_no_simultaneous_rational_3_and_5_torsion E
    (order15_gives_orders3_and5 E hord)

end MazurProof
