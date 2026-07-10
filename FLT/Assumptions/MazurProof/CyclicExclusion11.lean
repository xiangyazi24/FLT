import FLT.Assumptions.MazurProof.TorsionDefs
import FLT.Assumptions.MazurProof.TateOrder11
import FLT.Assumptions.MazurProof.RationalPointsN11
import FLT.Assumptions.MazurProof.RationalPointsN11Descent
import FLT.Assumptions.MazurProof.BillingMahlerField

/-!
# Cyclic order 11 exclusion

This file is deliberately independent of `CyclicOrderReduction.lean`: the
prime-order axiom `mazur_prime_torsion_bound` would exclude `11` immediately,
but using it here would make the exclusion circular for the present purpose.

Mathematically there are two standard routes.

* Modular curve route: `X₁(11)` is the elliptic curve
  `y² + y = x³ - x²` (Cremona label `11a3`).  It has rank `0` over `ℚ` and
  rational torsion `ℤ/5ℤ`; its rational points are cusps.  A rational point of
  order `11` on an elliptic curve over `ℚ` would give a noncuspidal rational
  point on `X₁(11)`, contradiction.
* Tate normal form route: after a rational change of variables, a curve with a
  rational point `P` of order `11` has Tate normal form
  `y² + (1-c)xy - by = x³ - bx²`, with `P = (0,0)`.  Evaluating the
  `11`-division condition at `(0,0)` gives a finite polynomial system in
  `b,c`; its rational solutions are exactly the order-`11` cases.  The final
  Diophantine computation has no rational solutions.

The Tate-normal-form and division-polynomial layers below are proved.  The
single remaining input is the rational-point classification on `11a3`, stated
at the exact boundary where the cubic-field descent is still required.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

namespace CyclicExclusion11

/-! ## From the existing torsion predicate to a point -/

theorem point_of_order11_of_has_rational_point
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (hord : HasRationalPointOfOrder E 11) :
    ∃ P : (E⁄ℚ).Point, addOrderOf P = 11 :=
  hord

/-! ## Tate normal form -/

structure TateNormalFormParameters where
  b : ℚ
  c : ℚ

/--
The Tate normal form
`y² + (1-c)xy - by = x³ - bx²`, with the distinguished point `(0,0)`.
-/
def tateNormalFormCurve (T : TateNormalFormParameters) : WeierstrassCurve ℚ where
  a₁ := 1 - T.c
  a₂ := -T.b
  a₃ := -T.b
  a₄ := 0
  a₆ := 0

def tateDiscriminant (T : TateNormalFormParameters) : ℚ :=
  (tateNormalFormCurve T).Δ

def TateNormalFormNonsingular (T : TateNormalFormParameters) : Prop :=
  tateDiscriminant T ≠ 0

theorem tateNormalForm_isElliptic_of_nonsingular
    {T : TateNormalFormParameters} (hΔ : TateNormalFormNonsingular T) :
    (tateNormalFormCurve T).IsElliptic := by
  refine ⟨?_⟩
  exact isUnit_iff_ne_zero.mpr hΔ

theorem tate_origin_equation (T : TateNormalFormParameters) :
    WeierstrassCurve.Affine.Equation (tateNormalFormCurve T) (0 : ℚ) 0 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [tateNormalFormCurve]

noncomputable def tateOrigin (T : TateNormalFormParameters)
    [(tateNormalFormCurve T).IsElliptic] :
    WeierstrassCurve.Affine.Point (tateNormalFormCurve T) :=
  WeierstrassCurve.Affine.Point.mk (tate_origin_equation T)

/-- The distinguished point `(0,0)` on the Tate normal form has exact order `n`. -/
def TateOriginHasOrder (T : TateNormalFormParameters) (n : ℕ) : Prop :=
  ∃ hEll : (tateNormalFormCurve T).IsElliptic,
    letI := hEll
    addOrderOf (tateOrigin T) = n

/-! ## Polynomial systems in the Tate parameters -/

abbrev TateBCPolynomial : Type :=
  MvPolynomial (Fin 2) ℚ

/-- Variable `b` in the polynomial ring `ℚ[b,c]`. -/
noncomputable def bVar : TateBCPolynomial :=
  MvPolynomial.X 0

/-- Variable `c` in the polynomial ring `ℚ[b,c]`. -/
noncomputable def cVar : TateBCPolynomial :=
  MvPolynomial.X 1

/-- The compact order-11 factor as a polynomial in the formal variables `b,c`. -/
noncomputable def F11Polynomial : TateBCPolynomial :=
  (cVar ^ 3 - bVar * (bVar - cVar)) * (bVar - cVar) ^ 3 -
    bVar * cVar * (bVar - cVar - cVar ^ 2) ^ 3

noncomputable def evalBC (T : TateNormalFormParameters) (F : TateBCPolynomial) : ℚ :=
  MvPolynomial.eval (fun i : Fin 2 => if i = 0 then T.b else T.c) F

@[simp] theorem evalBC_bVar (T : TateNormalFormParameters) :
    evalBC T bVar = T.b := by
  simp [evalBC, bVar]

@[simp] theorem evalBC_cVar (T : TateNormalFormParameters) :
    evalBC T cVar = T.c := by
  simp [evalBC, cVar]

@[simp] theorem evalBC_F11Polynomial (T : TateNormalFormParameters) :
    evalBC T F11Polynomial = TateNFDivision.F11 T.b T.c := by
  simp [evalBC, F11Polynomial, bVar, cVar, TateNFDivision.F11]

structure TatePolynomialSystem where
  equations : List TateBCPolynomial
  inequations : List TateBCPolynomial

def TatePolynomialSystem.SatisfiesEquations
    (S : TatePolynomialSystem) (T : TateNormalFormParameters) : Prop :=
  ∀ F, F ∈ S.equations → evalBC T F = 0

def TatePolynomialSystem.SatisfiesInequations
    (S : TatePolynomialSystem) (T : TateNormalFormParameters) : Prop :=
  ∀ F, F ∈ S.inequations → evalBC T F ≠ 0

/--
A rational solution of a Tate polynomial system.  The equations are the
cross-multiplied division-polynomial equations; the inequations record
nonsingularity and exact-order exclusions such as lower multiples not being
the identity.
-/
def TatePolynomialSystem.IsSolution
    (S : TatePolynomialSystem) (T : TateNormalFormParameters) : Prop :=
  TateNormalFormNonsingular T ∧
    S.SatisfiesEquations T ∧
    S.SatisfiesInequations T

/--
A polynomial system whose solutions are known to produce a Tate normal form
whose origin has exact order `11`.  A future concrete version should fill
`equations` with the evaluated `11`-division polynomial conditions and
`inequations` with the nondegeneracy/exactness conditions.
-/
structure TateOrder11PolynomialSystem extends TatePolynomialSystem where
  sound :
    ∀ T : TateNormalFormParameters,
      toTatePolynomialSystem.IsSolution T →
        TateOriginHasOrder T 11

def TateOrder11PolynomialSystem.IsSolution
    (S : TateOrder11PolynomialSystem) (T : TateNormalFormParameters) : Prop :=
  S.toTatePolynomialSystem.IsSolution T

theorem tate_origin_order11_of_system_solution
    (S : TateOrder11PolynomialSystem) {T : TateNormalFormParameters}
    (hT : S.IsSolution T) :
    TateOriginHasOrder T 11 :=
  S.sound T hT

/--
The canonical order-11 polynomial system: `F11(b,c)=0`, with `b≠0` and
nonsingularity.  Its soundness is proved through the checked division-polynomial
formula, not postulated as part of the data.
-/
noncomputable def canonicalOrder11System : TateOrder11PolynomialSystem where
  equations := [F11Polynomial]
  inequations := [bVar]
  sound := by
    intro T hT
    rcases hT with ⟨hΔ, heq, hineq⟩
    have hb : T.b ≠ 0 := by
      have h := hineq bVar (by simp)
      simpa using h
    have hF11 : TateNFDivision.F11 T.b T.c = 0 := by
      have h := heq F11Polynomial (by simp)
      simpa using h
    let hEll : (tateNormalFormCurve T).IsElliptic :=
      tateNormalForm_isElliptic_of_nonsingular hΔ
    refine ⟨hEll, ?_⟩
    letI : (tateNormalFormCurve T).IsElliptic := hEll
    let hEllOrder :
        (Scratch.TateZ2xZ10Reduction.tateNormalFormCurve T.b T.c).IsElliptic := by
      simpa [CyclicExclusion11.tateNormalFormCurve,
        Scratch.TateZ2xZ10Reduction.tateNormalFormCurve] using hEll
    letI :
        (Scratch.TateZ2xZ10Reduction.tateNormalFormCurve T.b T.c).IsElliptic :=
      hEllOrder
    have hord : addOrderOf (TateOrder11.tateOrigin T.b T.c) = 11 :=
      TateOrder11.tateOrigin_order_eleven_of_F11_eq_zero T.b T.c hb hF11
    have horigin :
        @tateOrigin T hEll =
          @TateOrder11.tateOrigin T.b T.c hEllOrder := by
      change WeierstrassCurve.Affine.Point.some 0 0 _ =
        WeierstrassCurve.Affine.Point.some 0 0 _
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨rfl, rfl⟩
    rw [horigin]
    exact hord

/-! ## The Tate bridge and the remaining arithmetic boundary -/

/--
Tate normal form and division-polynomial bridge.

Starting from an elliptic curve over `ℚ` with a rational point of exact order
`11`, one changes variables so the point is `(0,0)` on Tate normal form and
then evaluates the `11`-division condition at the origin.  The resulting
parameters solve the corresponding finite polynomial system in `b,c`.
-/
theorem tate_polynomial_system_solution_of_order11
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hord : HasRationalPointOfOrder E 11) :
    ∃ S : TateOrder11PolynomialSystem,
      ∃ T : TateNormalFormParameters, S.IsSolution T := by
  obtain ⟨P, hP⟩ := point_of_order11_of_has_rational_point hord
  obtain ⟨b, c, hEll, _hord, hb, hF11⟩ :=
    TateOrder11.exists_tate_parameters_of_order_eleven E P hP
  let T : TateNormalFormParameters := ⟨b, c⟩
  refine ⟨canonicalOrder11System, T, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · change (tateNormalFormCurve T).Δ ≠ 0
    simpa [T, CyclicExclusion11.tateNormalFormCurve,
      Scratch.TateZ2xZ10Reduction.tateNormalFormCurve] using
        (isUnit_iff_ne_zero.mp hEll.isUnit)
  · intro F hF
    simp only [canonicalOrder11System, List.mem_singleton] at hF
    subst F
    simpa [T] using hF11
  · intro F hF
    simp only [canonicalOrder11System, List.mem_singleton] at hF
    subst F
    simpa [T] using hb

/--
The remaining global input in the Billing--Mahler proof, after denominator
normalization and all explicit cubic-field algebra.

For a primitive integral model, either the original rational point is an
integral Lutz--Nagell exceptional point, or the principal-ideal descent puts
the cubic factor in the `epsilon` squareclass.  The class-number-one theorem,
the integral basis, the four unit squareclasses, and the coefficient expansion
are proved in `BillingMahlerField`.
-/
theorem billing_mahler_global_descent
    {ξ η : ℚ} (hcurve : RationalPointsN11Descent.MordellEquation ξ η)
    (x z y : ℤ) (hz : 0 < z) (hcop : Int.gcd x z = 1)
    (hξ : ξ = (x : ℚ) / (z : ℚ) ^ 2)
    (hmodel : y ^ 2 = x ^ 3 - 432 * x * z ^ 4 + 8208 * z ^ 6) :
    (∃ x y : ℤ,
      ξ = (x : ℚ) ∧ η = (y : ℚ) ∧
        (y ^ 2 = 0 ∨ y ^ 2 ∣
          (RationalPointsN11Descent.mordellDiscriminantAbs : ℤ))) ∨
      ∃ I : Ideal (NumberField.RingOfIntegers BillingMahlerField.K),
        y ≠ 0 ∧
          Ideal.span ({BillingMahlerField.descentInteger x z} :
              Set (NumberField.RingOfIntegers BillingMahlerField.K)) = I ^ 2 ∧
          ¬ IsSquare (BillingMahlerField.descentElement x z) := by
  sorry

/-- The global seam above implies the exact arithmetic dichotomy consumed by
the already-checked exceptional enumeration and parity contradiction. -/
theorem billing_mahler_rational_point_dichotomy
    {ξ η : ℚ} (hcurve : RationalPointsN11Descent.MordellEquation ξ η) :
    (∃ x y : ℤ,
      ξ = (x : ℚ) ∧ η = (y : ℚ) ∧
        (y ^ 2 = 0 ∨ y ^ 2 ∣
          (RationalPointsN11Descent.mordellDiscriminantAbs : ℤ))) ∨
      ∃ x z a b c : ℤ,
        Int.gcd x z = 1 ∧
          -x + 24 * z ^ 2 = a ^ 2 + 4 * b * c ∧
          18 * z ^ 2 = c ^ 2 + 2 * a * b + 4 * b * c ∧
          x = 2 * (b ^ 2 + c ^ 2 + a * c + 3 * z ^ 2) := by
  obtain ⟨x, z, y, hz, hcop, hξ, hmodel⟩ :=
    RationalPointsN11Descent.mordell_integral_model_of_rational_point ξ η hcurve
  rcases billing_mahler_global_descent hcurve x z y hz hcop hξ hmodel with
    hexceptional | ⟨I, hy, hideal, hnonsquare⟩
  · exact Or.inl hexceptional
  · have hnorm : 0 < Algebra.norm ℚ (BillingMahlerField.descentElement x z) := by
      rw [BillingMahlerField.norm_descentElement, ← hmodel]
      exact_mod_cast sq_pos_of_ne_zero hy
    obtain ⟨w, hw⟩ :=
      BillingMahlerField.descentElement_eq_epsilon_mul_integral_sq_of_ideal_square
        x z I hideal hnonsquare hnorm
    obtain ⟨a, b, c, habc⟩ :=
      BillingMahlerField.ringOfIntegers_exists_thetaBasis_coords
        (BillingMahlerField.epsilonInteger * w)
    have hsquare :
        BillingMahlerField.epsilon * BillingMahlerField.descentElement x z =
          BillingMahlerField.thetaBasisElement a b c ^ 2 := by
      calc
        BillingMahlerField.epsilon * BillingMahlerField.descentElement x z =
            BillingMahlerField.epsilon *
              (BillingMahlerField.epsilon * (w : BillingMahlerField.K) ^ 2) := by
                rw [hw]
        _ = (((BillingMahlerField.epsilonInteger * w :
              NumberField.RingOfIntegers BillingMahlerField.K) :
                BillingMahlerField.K)) ^ 2 := by
              simp
              ring
        _ = BillingMahlerField.thetaBasisElement a b c ^ 2 := by rw [habc]
    have hcoeff :=
      BillingMahlerField.coefficient_system_of_epsilon_mul_descentElement_eq_sq
        x z a b c hsquare
    exact Or.inr ⟨x, z, a, b, c, hcop, hcoeff.1, hcoeff.2.1, hcoeff.2.2⟩

/-- Every rational affine point on `11a3` is one of its four affine cusps. -/
theorem E11_rational_points_boundary
    {X Y : ℚ} (hcurve : RationalPointsN11.E11AffineEquation X Y) :
    RationalPointsN11.E11DegenerateParameter X := by
  have hmordell : RationalPointsN11Descent.MordellEquation
      (9 * X + 24) (27 * Y) :=
    RationalPointsN11Descent.mordellEquation_of_E11 hcurve
  rcases billing_mahler_rational_point_dichotomy hmordell with hexceptional | hordinary
  · obtain ⟨x, y, hx, _hy, hyDiscr⟩ := hexceptional
    have hxBoundary : x = -12 ∨ x = 24 :=
      RationalPointsN11Descent.exceptional_integral_point_boundary x y
        (by
          have := hmordell
          rw [hx, _hy] at this
          have hrat : (y : ℚ) ^ 2 =
              (x : ℚ) ^ 3 - 432 * (x : ℚ) + 8208 := by
            simpa [RationalPointsN11Descent.MordellEquation] using this
          exact_mod_cast hrat)
        hyDiscr
    unfold RationalPointsN11.E11DegenerateParameter
    rcases hxBoundary with rfl | rfl
    · right
      norm_num at hx
      linarith
    · left
      norm_num at hx
      linarith
  · obtain ⟨x, z, a, b, c, hcop, hfirst, hmid, hthird⟩ := hordinary
    exact (RationalPointsN11Descent.no_billing_mahler_coefficient_system
      x z a b c hcop hfirst hmid hthird).elim

private lemma tateDiscriminant_zero_of_b_eq_zero
    {T : TateNormalFormParameters} (hb : T.b = 0) :
    tateDiscriminant T = 0 := by
  unfold tateDiscriminant tateNormalFormCurve
  simp [hb, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem no_tate_order11_polynomial_solution
    (S : TateOrder11PolynomialSystem) :
    ¬ ∃ T : TateNormalFormParameters, S.IsSolution T := by
  rintro ⟨T, hT⟩
  have hb : T.b ≠ 0 := by
    intro hb0
    exact hT.1 (tateDiscriminant_zero_of_b_eq_zero hb0)
  obtain ⟨hEll, hord⟩ := S.sound T hT
  letI : (tateNormalFormCurve T).IsElliptic := hEll
  let hEllOrder :
      (Scratch.TateZ2xZ10Reduction.tateNormalFormCurve T.b T.c).IsElliptic := by
    simpa [CyclicExclusion11.tateNormalFormCurve,
      Scratch.TateZ2xZ10Reduction.tateNormalFormCurve] using hEll
  letI :
      (Scratch.TateZ2xZ10Reduction.tateNormalFormCurve T.b T.c).IsElliptic :=
    hEllOrder
  have horigin : addOrderOf (TateOrder11.tateOrigin T.b T.c) = 11 := by
    have heq :
        @tateOrigin T hEll =
          @TateOrder11.tateOrigin T.b T.c hEllOrder := by
      change WeierstrassCurve.Affine.Point.some 0 0 _ =
        WeierstrassCurve.Affine.Point.some 0 0 _
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨rfl, rfl⟩
    rw [← heq]
    exact hord
  have hF11 : TateNFDivision.F11 T.b T.c = 0 :=
    TateOrder11.F11_eq_zero_of_tateOrigin_order_eleven
      T.b T.c hb horigin
  exact
    (RationalPointsN11.no_F11_solution_of_E11_boundary
      (@E11_rational_points_boundary)) ⟨T.b, T.c, hb, hF11⟩

end CyclicExclusion11

/-- No elliptic curve over `ℚ` has a rational point of exact order `11`. -/
theorem no_rational_point_of_order_11
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 11 := by
  intro hord
  obtain ⟨S, T, hT⟩ :=
    CyclicExclusion11.tate_polynomial_system_solution_of_order11 E hord
  exact CyclicExclusion11.no_tate_order11_polynomial_solution S ⟨T, hT⟩

end MazurProof
