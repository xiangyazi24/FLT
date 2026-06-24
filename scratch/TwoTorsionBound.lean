import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# A first formal bound on rational 2-torsion of a Weierstrass curve

This scratch file proves the geometric core: an affine point killed by doubling
has `y = negY x y`, hence its `x`-coordinate is a root of the usual cubic
`4x^3 + b₂x² + 2b₄x + b₆`.
-/

open scoped WeierstrassCurve.Affine
open Polynomial

namespace Scratch.TwoTorsionBound

noncomputable section

abbrev AffinePoint (W : WeierstrassCurve ℚ) :=
  WeierstrassCurve.Affine.Point W

/-- The cubic whose roots are the affine 2-torsion `x`-coordinates. -/
def twoTorsionCubic (W : WeierstrassCurve ℚ) : ℚ[X] :=
  C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆

lemma twoTorsionCubic_eval (W : WeierstrassCurve ℚ) (x : ℚ) :
    (twoTorsionCubic W).eval x =
      4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  simp [twoTorsionCubic]

lemma twoTorsionCubic_ne_zero (W : WeierstrassCurve ℚ) :
    twoTorsionCubic W ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : ℚ[X] => p.coeff 3) h
  norm_num [twoTorsionCubic] at hcoeff

lemma twoTorsionCubic_natDegree_le (W : WeierstrassCurve ℚ) :
    (twoTorsionCubic W).natDegree ≤ 3 := by
  simpa [twoTorsionCubic] using
    (Polynomial.natDegree_cubic_le (a := (4 : ℚ)) (b := W.b₂)
      (c := 2 * W.b₄) (d := W.b₆))

lemma affine_two_torsion_y_eq_negY
    {W : WeierstrassCurve ℚ} [W.IsElliptic] {x y : ℚ}
    {h : WeierstrassCurve.Affine.Nonsingular W x y}
    (h2 : (WeierstrassCurve.Affine.Point.some x y h : AffinePoint W) +
        WeierstrassCurve.Affine.Point.some x y h = 0) :
    y = WeierstrassCurve.Affine.negY W x y := by
  by_contra hy
  have hs : (WeierstrassCurve.Affine.Point.some x y h : AffinePoint W) +
        WeierstrassCurve.Affine.Point.some x y h =
      WeierstrassCurve.Affine.Point.some _ _
        (WeierstrassCurve.Affine.nonsingular_add h h (fun hxy => hy hxy.right)) := by
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy
  rw [h2] at hs
  exact WeierstrassCurve.Affine.Point.some_ne_zero _ hs.symm

lemma affine_two_torsion_linear_relation
    {W : WeierstrassCurve ℚ} [W.IsElliptic] {x y : ℚ}
    {h : WeierstrassCurve.Affine.Nonsingular W x y}
    (h2 : (WeierstrassCurve.Affine.Point.some x y h : AffinePoint W) +
        WeierstrassCurve.Affine.Point.some x y h = 0) :
    2 * y + W.a₁ * x + W.a₃ = 0 := by
  have hy := affine_two_torsion_y_eq_negY (W := W) h2
  rw [WeierstrassCurve.Affine.negY] at hy
  linear_combination hy

lemma affine_two_torsion_cubic
    {W : WeierstrassCurve ℚ} [W.IsElliptic] {x y : ℚ}
    {h : WeierstrassCurve.Affine.Nonsingular W x y}
    (h2 : (WeierstrassCurve.Affine.Point.some x y h : AffinePoint W) +
        WeierstrassCurve.Affine.Point.some x y h = 0) :
    (twoTorsionCubic W).eval x = 0 := by
  rw [twoTorsionCubic_eval]
  have heq : WeierstrassCurve.Affine.Equation W x y := h.1
  have hrel := affine_two_torsion_linear_relation (W := W) h2
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  rw [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  nlinarith

lemma affine_two_torsion_same_x
    {W : WeierstrassCurve ℚ} [W.IsElliptic] {x y₁ y₂ : ℚ}
    {h₁ : WeierstrassCurve.Affine.Nonsingular W x y₁}
    {h₂ : WeierstrassCurve.Affine.Nonsingular W x y₂}
    (ht₁ : (WeierstrassCurve.Affine.Point.some x y₁ h₁ : AffinePoint W) +
        WeierstrassCurve.Affine.Point.some x y₁ h₁ = 0)
    (ht₂ : (WeierstrassCurve.Affine.Point.some x y₂ h₂ : AffinePoint W) +
        WeierstrassCurve.Affine.Point.some x y₂ h₂ = 0) :
    (WeierstrassCurve.Affine.Point.some x y₁ h₁ : AffinePoint W) =
      WeierstrassCurve.Affine.Point.some x y₂ h₂ := by
  have hr₁ := affine_two_torsion_linear_relation (W := W) ht₁
  have hr₂ := affine_two_torsion_linear_relation (W := W) ht₂
  have hy : y₁ = y₂ := by nlinarith
  subst hy
  rfl

abbrev TwoTorsionPoint (W : WeierstrassCurve ℚ) [W.IsElliptic] :=
  {P : AffinePoint W // P + P = 0}

noncomputable def encodeTwoTorsion (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (P : TwoTorsionPoint W) : Option ((twoTorsionCubic W).rootSet ℚ) :=
  match hP : P.1 with
  | 0 => none
  | WeierstrassCurve.Affine.Point.some x y h =>
      some ⟨x, by
        have h2 : (WeierstrassCurve.Affine.Point.some x y h : AffinePoint W) +
            WeierstrassCurve.Affine.Point.some x y h = 0 := by
          simpa [hP] using P.2
        have hroot := affine_two_torsion_cubic (W := W) (x := x) (y := y) (h := h) h2
        rw [Polynomial.mem_rootSet_of_ne (twoTorsionCubic_ne_zero W)]
        simpa [IsRoot, aeval_def] using hroot⟩

theorem encodeTwoTorsion_injective (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    Function.Injective (encodeTwoTorsion W) := by
  rintro ⟨P, hP2⟩ ⟨Q, hQ2⟩ henc
  apply Subtype.ext
  change P = Q
  cases P with
  | zero =>
      cases Q with
      | zero =>
          rfl
      | some x₂ y₂ h₂ =>
          simp [encodeTwoTorsion] at henc
  | some x₁ y₁ h₁ =>
      cases Q with
      | zero =>
          simp [encodeTwoTorsion] at henc
      | some x₂ y₂ h₂ =>
          have hx : x₁ = x₂ := by
            simp [encodeTwoTorsion] at henc
            exact henc
          subst x₂
          have ht₁ : (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : AffinePoint W) +
              WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ = 0 := by
            exact hP2
          have ht₂ : (WeierstrassCurve.Affine.Point.some x₁ y₂ h₂ : AffinePoint W) +
              WeierstrassCurve.Affine.Point.some x₁ y₂ h₂ = 0 := by
            exact hQ2
          exact affine_two_torsion_same_x (W := W) (x := x₁) (y₁ := y₁) (y₂ := y₂)
            (h₁ := h₁) (h₂ := h₂) ht₁ ht₂

noncomputable instance twoTorsionPoint_fintype
    (W : WeierstrassCurve ℚ) [W.IsElliptic] : Fintype (TwoTorsionPoint W) :=
  Fintype.ofInjective (encodeTwoTorsion W) (encodeTwoTorsion_injective W)

theorem card_twoTorsionPoint_le_four (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    Fintype.card (TwoTorsionPoint W) ≤ 4 := by
  classical
  have hencode :
      Fintype.card (TwoTorsionPoint W) ≤
        Fintype.card (Option ((twoTorsionCubic W).rootSet ℚ)) :=
    Fintype.card_le_of_injective (encodeTwoTorsion W) (encodeTwoTorsion_injective W)
  have hroots :
      Fintype.card ((twoTorsionCubic W).rootSet ℚ) ≤ 3 := by
    rw [Set.fintypeCard_eq_ncard]
    exact (Polynomial.ncard_rootSet_le (twoTorsionCubic W) ℚ).trans
      (twoTorsionCubic_natDegree_le W)
  calc
    Fintype.card (TwoTorsionPoint W)
        ≤ Fintype.card (Option ((twoTorsionCubic W).rootSet ℚ)) := hencode
    _ = Fintype.card ((twoTorsionCubic W).rootSet ℚ) + 1 := by simp
    _ ≤ 4 := by omega

abbrev ZMod2Cube :=
  ZMod 2 × ZMod 2 × ZMod 2

lemma two_nsmul_zmod2cube (g : ZMod2Cube) : (2 : ℕ) • g = 0 := by
  ext <;> exact ZModModule.char_nsmul_eq_zero 2 _

theorem no_zmod2cube_injective_to_elliptic_point
    (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    ¬ ∃ f : ZMod2Cube →+ AffinePoint W, Function.Injective f := by
  rintro ⟨f, hf⟩
  let toTwoTorsion : ZMod2Cube → TwoTorsionPoint W := fun g =>
    ⟨f g, by
      have htwo : (2 : ℕ) • f g = 0 := by
        rw [← f.map_nsmul, two_nsmul_zmod2cube]
        simp
      simpa [two_nsmul] using htwo⟩
  have hto_inj : Function.Injective toTwoTorsion := by
    intro a b h
    apply hf
    exact congrArg Subtype.val h
  have hcard :
      Fintype.card ZMod2Cube ≤ Fintype.card (TwoTorsionPoint W) :=
    Fintype.card_le_of_injective toTwoTorsion hto_inj
  have hdomain : Fintype.card ZMod2Cube = 8 := by
    simp [ZMod2Cube, Fintype.card_prod, ZMod.card]
  have hcodomain : Fintype.card (TwoTorsionPoint W) ≤ 4 :=
    card_twoTorsionPoint_le_four W
  omega

end

end Scratch.TwoTorsionBound
