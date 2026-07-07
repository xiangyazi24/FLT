import FLT.Assumptions.MazurProof.TorsionDefs

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

The current file records the Tate-normal-form interface and leaves the two hard
inputs as `sorry`: the moduli/normal-form bridge, and the final Diophantine
elimination of the resulting polynomial system.
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

noncomputable def evalBC (T : TateNormalFormParameters) (F : TateBCPolynomial) : ℚ :=
  MvPolynomial.eval (fun i : Fin 2 => if i = 0 then T.b else T.c) F

@[simp] theorem evalBC_bVar (T : TateNormalFormParameters) :
    evalBC T bVar = T.b := by
  simp [evalBC, bVar]

@[simp] theorem evalBC_cVar (T : TateNormalFormParameters) :
    evalBC T cVar = T.c := by
  simp [evalBC, cVar]

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

/-! ## The two remaining hard inputs -/

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
  sorry

/--
Final Diophantine input for the Tate normal form route.

The concrete `11`-division polynomial system in `b,c` has no rational solution.
This is the Tate-normal-form replacement for the rank-`0` computation on
`X₁(11)`.
-/
theorem no_tate_order11_polynomial_solution
    (S : TateOrder11PolynomialSystem) :
    ¬ ∃ T : TateNormalFormParameters, S.IsSolution T := by
  sorry

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
