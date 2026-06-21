
═══ BRIDGE  Q19 →dm4  SUBMITTED ═══
     "A6-HEIGHT design R5 (this is about WEIL HEIGHTS / the DUPLICATION MAP …"
     ↳ debug: task ad35990e

[ask-gpt Q19 dm4 tid=ad35990e +0s] dispatched, waiting for answer
[ask-gpt Q19 dm4 tid=ad35990e +90s] waiting (status=processing)
[ask-gpt Q19 dm4 tid=ad35990e +180s] waiting (status=processing)
[ask-gpt Q19 dm4 tid=ad35990e +270s] waiting (status=processing)
[ask-gpt Q19 dm4 tid=ad35990e +360s] waiting (status=processing)
[ask-gpt Q19 dm4 tid=ad35990e +450s] waiting (status=processing)
[ask-gpt Q19 dm4 tid=ad35990e +540s] waiting (status=processing)
[ask-gpt Q19 dm4 tid=ad35990e +630s] waiting (status=processing)
[ask-gpt Q19 dm4 tid=ad35990e +651s] terminal: status=completed

═══ BRIDGE  Q19 →dm4  ✅ COMPLETE (8.3KB, 10m51s) ═══
     "A6-HEIGHT design R5 (this is about WEIL HEIGHTS / the DUPLICATION MAP …"
     ↳ debug: task ad35990e

I’ll first pin the current affine point/group-law API, since the duplication proof depends on exact xRep, add_self, slope/addX/negY, and equation lemmas.

The live API has the needed doubling case lemmas and xRep facts, but no projective duplication theorem. I’ll prove it directly from slope/addX, with vertical and nonvertical algebra lemmas.

Mathlib’s current affine API has the needed point constructors and group-law split: Point.add_self_of_Y_eq gives the vertical/2-torsion case, and Point.add_self_of_Y_ne gives the tangent case. It also has Point.xRep with 0 ↦ ![1,0] and some x y h ↦ ![x,1]. 
GitHub
 
GitHub
 The formula API exposes negY, slope, and addX, with tangent slope denominator y - W.negY x y, and addX x x ℓ = ℓ^2 + a₁ℓ - a₂ - x - x. 
GitHub
 
GitHub

Below I use this SameP1 orientation:

lean
def SameP1 (u v : Fin 2 → ℚ) : Prop :=
  ∃ c : ℚ, c ≠ 0 ∧ v = c • u

So the right-hand projective vector is a nonzero scalar multiple of the left-hand one. If your local SameP1 is reversed, use the inverse witnesses c⁻¹ in the nonzero cases.

lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

open WeierstrassCurve
open WeierstrassCurve.Affine
open scoped Matrix

namespace WeierstrassCurve

noncomputable def dupNumH (W : WeierstrassCurve ℚ) (X Z : ℚ) : ℚ :=
  X ^ 4 - W.b₄ * X ^ 2 * Z ^ 2 - 2 * W.b₆ * X * Z ^ 3 - W.b₈ * Z ^ 4

noncomputable def dupDenH (W : WeierstrassCurve ℚ) (X Z : ℚ) : ℚ :=
  4 * X ^ 3 * Z + W.b₂ * X ^ 2 * Z ^ 2 + 2 * W.b₄ * X * Z ^ 3 + W.b₆ * Z ^ 4

/-- Same projective point in `ℙ¹`, oriented as:
`SameP1 u v` means `v = c • u` for some nonzero scalar `c`. -/
def SameP1 (u v : Fin 2 → ℚ) : Prop :=
  ∃ c : ℚ, c ≠ 0 ∧ v = c • u

namespace SameP1

lemma mk_vec
    {u v : Fin 2 → ℚ} {c : ℚ}
    (hc : c ≠ 0)
    (h0 : v 0 = c * u 0)
    (h1 : v 1 = c * u 1) :
    SameP1 u v := by
  refine ⟨c, hc, ?_⟩
  ext i
  fin_cases i
  · simpa [Pi.smul_apply] using h0
  · simpa [Pi.smul_apply] using h1

lemma rfl_vec (u : Fin 2 → ℚ) (hu : u ≠ 0) :
    SameP1 u u := by
  refine ⟨1, one_ne_zero, ?_⟩
  ext i
  simp

end SameP1

namespace AffineDup

variable (W : WeierstrassCurve ℚ) [W.IsElliptic]

private lemma dupDenH_eq_Yder_sq
    {x y : ℚ} (hE : W.Equation x y) :
    dupDenH W x 1 = (y - W.negY x y) ^ 2 := by
  have hE0 : y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 := by
    simpa [Affine.equation_iff'] using hE
  rw [dupDenH, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, Affine.negY]
  linear_combination (norm := ring1) -4 * hE0

private lemma dupNumH_eq_polynomialX_sq_of_Yder_zero
    {x y : ℚ} (hE : W.Equation x y)
    (hY : y - W.negY x y = 0) :
    dupNumH W x 1 =
      (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) ^ 2 := by
  have hE0 : y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 := by
    simpa [Affine.equation_iff'] using hE
  have hY0 : 2 * y + W.a₁ * x + W.a₃ = 0 := by
    simpa [Affine.negY, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hY
  rw [dupNumH, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  linear_combination (norm := ring1)
      (W.a₁ ^ 2 + 4 * W.a₂ + 8 * x) * hE0
    + (-(W.a₁ ^ 2) * y + W.a₁ * W.a₂ * x + W.a₁ * W.a₄
        + W.a₁ * x ^ 2 - W.a₂ * W.a₃ - 2 * W.a₂ * y
        - 2 * W.a₃ * x - 4 * x * y) * hY0

private lemma dupNumH_eq_dupDenH_mul_addX_of_Yder_ne
    {x y : ℚ} (hE : W.Equation x y)
    (hy : y ≠ W.negY x y) :
    dupNumH W x 1 =
      dupDenH W x 1 * W.addX x x (W.slope x x y y) := by
  have hE0 : y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 := by
    simpa [Affine.equation_iff'] using hE
  have hden : y - W.negY x y ≠ 0 := sub_ne_zero.mpr hy
  rw [dupNumH, dupDenH, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, Affine.addX]
  rw [Affine.slope_of_Y_ne (W := W) rfl hy]
  field_simp [hden]
  rw [Affine.negY]
  linear_combination (norm := ring1)
    (W.a₁ ^ 2 * x + W.a₁ * W.a₃ + 4 * W.a₂ * x
      + 2 * W.a₄ + 6 * x ^ 2) ^ 2 * hE0

private lemma dupNumH_ne_zero_of_Yder_zero
    {x y : ℚ} (h : W.Nonsingular x y)
    (hY : y - W.negY x y = 0) :
    dupNumH W x 1 ≠ 0 := by
  have hYpoly : W.polynomialY.evalEval x y = 0 := by
    simpa [Affine.evalEval_polynomialY, Affine.negY,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hY
  have hXpoly : W.polynomialX.evalEval x y ≠ 0 :=
    h.2.resolve_right hYpoly
  have hX :
      W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ≠ 0 := by
    simpa [Affine.evalEval_polynomialX] using hXpoly
  have hN := dupNumH_eq_polynomialX_sq_of_Yder_zero
    (W := W) h.1 hY
  rw [hN]
  exact pow_ne_zero 2 hX

/--
Projective duplication formula for the x-coordinate representative.

This version is stated for `P : W.Point`. For the FLT convention
`P : (W⁄ℚ).Point`, apply this theorem to `W⁄ℚ` and then `simpa [dupNumH, dupDenH]`.
-/
theorem xRep_two_nsmul_same_dup_affine
    (P : W.Point) :
    SameP1 ((2 • P).xRep)
      ![dupNumH W (P.xRep 0) (P.xRep 1),
        dupDenH W (P.xRep 0) (P.xRep 1)] := by
  classical
  rcases P with _ | ⟨x, y, h⟩
  · -- `P = 0`
    refine SameP1.mk_vec (u := ((2 • (0 : W.Point)).xRep))
      (v := ![dupNumH W ((0 : W.Point).xRep 0) ((0 : W.Point).xRep 1),
        dupDenH W ((0 : W.Point).xRep 0) ((0 : W.Point).xRep 1)])
      (c := 1) one_ne_zero ?_ ?_
    · simp [dupNumH]
    · simp [dupDenH]
  · by_cases hy : y = W.negY x y
    · -- vertical tangent / nonzero 2-torsion: `2P = 0`
      have hY : y - W.negY x y = 0 := sub_eq_zero.mpr hy
      have htwo :
          2 • (Point.some x y h : W.Point) = 0 := by
        simpa [two_nsmul] using
          (Point.add_self_of_Y_eq (W := W) (h₁ := h) hy)
      have hD0 : dupDenH W x 1 = 0 := by
        rw [dupDenH_eq_Yder_sq (W := W) h.1, hY]
        norm_num
      have hN0 : dupNumH W x 1 ≠ 0 :=
        dupNumH_ne_zero_of_Yder_zero (W := W) h hY
      refine SameP1.mk_vec
        (u := ((2 • (Point.some x y h : W.Point)).xRep))
        (v := ![dupNumH W ((Point.some x y h).xRep 0) ((Point.some x y h).xRep 1),
          dupDenH W ((Point.some x y h).xRep 0) ((Point.some x y h).xRep 1)])
        (c := dupNumH W x 1) hN0 ?_ ?_
      · simp [htwo]
      · simp [htwo, hD0]
    · -- tangent case: denominator nonzero and witness is the denominator
      have hYne : y - W.negY x y ≠ 0 := sub_ne_zero.mpr hy
      have hD_eq : dupDenH W x 1 = (y - W.negY x y) ^ 2 :=
        dupDenH_eq_Yder_sq (W := W) h.1
      have hDne : dupDenH W x 1 ≠ 0 := by
        rw [hD_eq]
        exact pow_ne_zero 2 hYne
      have htwo :
          2 • (Point.some x y h : W.Point) =
            Point.some _ _ (Affine.nonsingular_add h h (fun hxy => hy hxy.right)) := by
        simpa [two_nsmul] using
          (Point.add_self_of_Y_ne (W := W) (h₁ := h) hy)
      have hN :
          dupNumH W x 1 =
            dupDenH W x 1 * W.addX x x (W.slope x x y y) :=
        dupNumH_eq_dupDenH_mul_addX_of_Yder_ne (W := W) h.1 hy
      refine SameP1.mk_vec
        (u := ((2 • (Point.some x y h : W.Point)).xRep))
        (v := ![dupNumH W ((Point.some x y h).xRep 0) ((Point.some x y h).xRep 1),
          dupDenH W ((Point.some x y h).xRep 0) ((Point.some x y h).xRep 1)])
        (c := dupDenH W x 1) hDne ?_ ?_
      · simp [htwo, hN]
      · simp [htwo]

/--
Wrapper in the `P : (W⁄ℚ).Point` style. The final `simpa` uses the base-change
simp lemmas for `b₂,b₄,b₆,b₈`.
-/
theorem xRep_two_nsmul_same_dup
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (P : (W⁄ℚ).Point) :
    SameP1 ((2 • P).xRep)
      ![dupNumH W (P.xRep 0) (P.xRep 1),
        dupDenH W (P.xRep 0) (P.xRep 1)] := by
  simpa [dupNumH, dupDenH] using
    xRep_two_nsmul_same_dup_affine (W := W⁄ℚ) P

end AffineDup
end WeierstrassCurve

The non-2-torsion algebraic heart is exactly this block:

lean
rw [dupNumH, dupDenH, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
  WeierstrassCurve.b₆, WeierstrassCurve.b₈, Affine.addX]
rw [Affine.slope_of_Y_ne (W := W) rfl hy]
field_simp [hden]
rw [Affine.negY]
linear_combination (norm := ring1)
  (W.a₁ ^ 2 * x + W.a₁ * W.a₃ + 4 * W.a₂ * x
    + 2 * W.a₄ + 6 * x ^ 2) ^ 2 * hE0

The 2-torsion confirmation is:

lean
dupDenH W x 1 = (y - W.negY x y)^2 = 0

and

lean
dupNumH W x 1 =
  (W.a₁ * y - (3*x^2 + 2*W.a₂*x + W.a₄))^2 ≠ 0

because y - W.negY x y = 0 is exactly W.polynomialY.evalEval x y = 0, while nonsingularity forces W.polynomialX.evalEval x y ≠ 0.
