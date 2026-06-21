import Mathlib

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.overlappingInstances false

open Polynomial
open WeierstrassCurve
open WeierstrassCurve.Affine

noncomputable section

namespace KeystoneLadder

universe u

variable {k : Type u} [Field k] [DecidableEq k]

/-- Minimal projective x-coordinate over an arbitrary field. -/
structure P1 (k : Type u) [Zero k] where
  X : k
  Z : k
  not_both_zero : X ≠ 0 ∨ Z ≠ 0

namespace P1

variable [Field k]

/-- Equality in `P¹`, by cross multiplication. -/
def Same (A B : P1 k) : Prop :=
  A.X * B.Z = B.X * A.Z

@[simp] lemma same_refl (A : P1 k) : Same A A := by
  dsimp [Same]

@[simp] lemma same_mk_iff {A B : P1 k} :
    Same A B ↔ A.X * B.Z = B.X * A.Z := Iff.rfl

/-- Convert the bundled nonzero `P¹` representative to Mathlib's `Fin 2` convention. -/
def toVec (A : P1 k) : Fin 2 → k :=
  ![A.X, A.Z]

end P1

variable (E : WeierstrassCurve k)

/-- The point at infinity on the Kummer line. -/
def xInf : P1 k :=
  { X := 1, Z := 0, not_both_zero := Or.inl one_ne_zero }

/-- The affine x-coordinate `[x : 1]`. -/
def xAff (x : k) : P1 k :=
  { X := x, Z := 1, not_both_zero := Or.inr one_ne_zero }

/-- Projective x-coordinate. The group identity maps to `[1 : 0]`. -/
def xRep : E.toAffine.Point → P1 k
  | 0 => xInf
  | Point.some x _ _ => xAff x

@[simp] lemma xRep_zero :
    xRep E (0 : E.toAffine.Point) = xInf := rfl

@[simp] lemma xRep_some {x y : k} (h : E.toAffine.Nonsingular x y) :
    xRep E (Point.some x y h : E.toAffine.Point) = xAff x := rfl

@[simp] lemma xRep_some_X {x y : k} (h : E.toAffine.Nonsingular x y) :
    (xRep E (Point.some x y h : E.toAffine.Point)).X = x := rfl

@[simp] lemma xRep_some_Z {x y : k} (h : E.toAffine.Nonsingular x y) :
    (xRep E (Point.some x y h : E.toAffine.Point)).Z = 1 := rfl

@[simp] lemma xInf_X : (xInf : P1 k).X = 1 := rfl
@[simp] lemma xInf_Z : (xInf : P1 k).Z = 0 := rfl
@[simp] lemma xAff_X (x : k) : (xAff x).X = x := rfl
@[simp] lemma xAff_Z (x : k) : (xAff x).Z = 1 := rfl

@[simp] lemma xRep_neg_some_same {x y : k} (h : E.toAffine.Nonsingular x y) :
    P1.Same
      (xRep E (-(Point.some x y h : E.toAffine.Point)))
      (xRep E (Point.some x y h : E.toAffine.Point)) := by
  simp [xRep, xAff, P1.Same]

lemma xRep_neg_same (P : E.toAffine.Point) :
    P1.Same (xRep E (-P)) (xRep E P) := by
  cases P with
  | zero =>
      rw [show -(Point.zero : E.toAffine.Point) = 0 by rfl]
      simp [xRep, xInf, P1.Same]
  | some x y h =>
      exact xRep_neg_some_same (E := E) h

/-- `δ = X₁Z₂ - X₂Z₁`. -/
def delta (A B : P1 k) : k :=
  A.X * B.Z - B.X * A.Z

/-- Homogeneous numerator for `x₊ + x₋`. -/
def sumNum (A B : P1 k) : k :=
    2 * A.X * B.X * (A.X * B.Z + B.X * A.Z)
  + E.b₂ * A.X * B.X * A.Z * B.Z
  + E.b₄ * A.Z * B.Z * (A.X * B.Z + B.X * A.Z)
  + E.b₆ * A.Z ^ 2 * B.Z ^ 2

lemma delta_eq_zero_of_same {A B : P1 k} (h : P1.Same A B) :
    delta A B = 0 := by
  dsimp [delta, P1.Same] at h ⊢
  linear_combination h

@[simp] lemma xRep_add_some_of_X_ne
    {x₁ y₁ x₂ y₂ : k}
    {h₁ : E.toAffine.Nonsingular x₁ y₁}
    {h₂ : E.toAffine.Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) :
    xRep E
      ((Point.some x₁ y₁ h₁ : E.toAffine.Point) + Point.some x₂ y₂ h₂)
      = xAff (E.toAffine.addX x₁ x₂ (E.toAffine.slope x₁ x₂ y₁ y₂)) := by
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (W := E.toAffine) hx]
  rfl

@[simp] lemma xRep_sub_some_of_X_ne
    {x₁ y₁ x₂ y₂ : k}
    {h₁ : E.toAffine.Nonsingular x₁ y₁}
    {h₂ : E.toAffine.Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) :
    xRep E
      ((Point.some x₁ y₁ h₁ : E.toAffine.Point) - Point.some x₂ y₂ h₂)
      = xAff (E.toAffine.addX x₁ x₂
          (E.toAffine.slope x₁ x₂ y₁ (E.toAffine.negY x₂ y₂))) := by
  rw [sub_eq_add_neg]
  rw [WeierstrassCurve.Affine.Point.neg_some (W' := E.toAffine) h₂]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (W := E.toAffine) hx]
  rfl

lemma xRep_add_sub_kummer_affine_sum_ne_x
    {x₁ y₁ x₂ y₂ : k}
    (h₁ : E.toAffine.Equation x₁ y₁)
    (h₂ : E.toAffine.Equation x₂ y₂)
    (hx : x₁ ≠ x₂) :
    let xp := E.toAffine.addX x₁ x₂ (E.toAffine.slope x₁ x₂ y₁ y₂)
    let xm := E.toAffine.addX x₁ x₂
      (E.toAffine.slope x₁ x₂ y₁ (E.toAffine.negY x₂ y₂))
    (x₁ - x₂) ^ 2 * (xp + xm) =
      2 * x₁ * x₂ * (x₁ + x₂) + E.b₂ * x₁ * x₂ + E.b₄ * (x₁ + x₂) + E.b₆ := by
  change
    (x₁ - x₂) ^ 2 *
      (E.toAffine.addX x₁ x₂ (E.toAffine.slope x₁ x₂ y₁ y₂) +
        E.toAffine.addX x₁ x₂
          (E.toAffine.slope x₁ x₂ y₁ (E.toAffine.negY x₂ y₂))) =
      2 * x₁ * x₂ * (x₁ + x₂) + E.b₂ * x₁ * x₂ + E.b₄ * (x₁ + x₂) + E.b₆
  rw [WeierstrassCurve.Affine.slope_of_X_ne (W := E.toAffine) hx]
  rw [WeierstrassCurve.Affine.slope_of_X_ne (W := E.toAffine) hx]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at *
  rw [WeierstrassCurve.Affine.equation_iff] at h₁ h₂
  field_simp [sub_ne_zero.mpr hx]
  linear_combination (norm := ring1) 2 * h₁ + 2 * h₂

lemma some_ext_of_xy_eq
    {x₁ y₁ x₂ y₂ : k}
    {h₁ : E.toAffine.Nonsingular x₁ y₁}
    {h₂ : E.toAffine.Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : E.toAffine.Point) = Point.some x₂ y₂ h₂ := by
  subst hx
  subst hy
  congr

lemma xRep_add_zero_of_Y_eq
    {x₁ y₁ x₂ y₂ : k}
    {h₁ : E.toAffine.Nonsingular x₁ y₁}
    {h₂ : E.toAffine.Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = E.toAffine.negY x₂ y₂) :
    xRep E ((Point.some x₁ y₁ h₁ : E.toAffine.Point) + Point.some x₂ y₂ h₂) = xInf := by
  rw [WeierstrassCurve.Affine.Point.add_of_Y_eq (W := E.toAffine) hx hy]
  rfl

lemma xRep_sub_zero_of_same_xy
    {x₁ y₁ x₂ y₂ : k}
    {h₁ : E.toAffine.Nonsingular x₁ y₁}
    {h₂ : E.toAffine.Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = y₂) :
    xRep E ((Point.some x₁ y₁ h₁ : E.toAffine.Point) - Point.some x₂ y₂ h₂) = xInf := by
  have hPQ : (Point.some x₁ y₁ h₁ : E.toAffine.Point) = Point.some x₂ y₂ h₂ :=
    some_ext_of_xy_eq (E := E) hx hy
  rw [hPQ]
  simp [xRep]

set_option maxHeartbeats 2000000 in
theorem xRep_add_sub_kummer_sum
    (P Q : E.toAffine.Point) :
    let A := xRep E P
    let B := xRep E Q
    let Xp := xRep E (P + Q)
    let Xm := xRep E (P - Q)
    let D := (delta A B) ^ 2
    D * (Xp.X * Xm.Z + Xm.X * Xp.Z)
      = sumNum E A B * Xp.Z * Xm.Z := by
  classical
  cases P with
  | zero =>
      cases Q with
      | zero =>
          simp [xRep, xInf, delta, sumNum]
      | some x₂ y₂ h₂ =>
          rw [show Point.zero + Point.some x₂ y₂ h₂ =
                (Point.some x₂ y₂ h₂ : E.toAffine.Point) by rfl]
          rw [show Point.zero - Point.some x₂ y₂ h₂ =
                -(Point.some x₂ y₂ h₂ : E.toAffine.Point) by rfl]
          simp [xRep, xInf, xAff, delta, sumNum]
          ring_nf
  | some x₁ y₁ h₁ =>
      cases Q with
      | zero =>
          rw [show Point.some x₁ y₁ h₁ + Point.zero =
                (Point.some x₁ y₁ h₁ : E.toAffine.Point) by rfl]
          rw [show Point.some x₁ y₁ h₁ - Point.zero =
                (Point.some x₁ y₁ h₁ : E.toAffine.Point) by rfl]
          simp [xRep, xInf, xAff, delta, sumNum]
          ring_nf
      | some x₂ y₂ h₂ =>
          by_cases hx_eq : x₁ = x₂
          · have hY := WeierstrassCurve.Affine.Y_eq_of_X_eq
                (W := E.toAffine) h₁.left h₂.left hx_eq
            rcases hY with hy_same | hy_neg
            · subst x₁
              subst y₁
              have hsub0 :
                  xRep E
                    ((Point.some x₂ y₂ h₁ : E.toAffine.Point) - Point.some x₂ y₂ h₂) = xInf :=
                xRep_sub_zero_of_same_xy (E := E) rfl rfl
              rw [hsub0]
              simp [xRep, xAff, xInf, delta, sumNum]
            · subst x₁
              have hadd0 :
                  xRep E
                    ((Point.some x₂ y₁ h₁ : E.toAffine.Point) + Point.some x₂ y₂ h₂) = xInf :=
                xRep_add_zero_of_Y_eq (E := E) rfl hy_neg
              rw [hadd0]
              simp [xRep, xAff, xInf, delta, sumNum]
          · have hx : x₁ ≠ x₂ := hx_eq
            have hsum := xRep_add_sub_kummer_affine_sum_ne_x
              (E := E) h₁.left h₂.left hx
            rw [xRep_add_some_of_X_ne (E := E) (h₁ := h₁) (h₂ := h₂) hx,
              xRep_sub_some_of_X_ne (E := E) (h₁ := h₁) (h₂ := h₂) hx]
            simp [xRep, xAff, delta, sumNum] at hsum ⊢
            ring_nf at hsum ⊢
            exact hsum

lemma xRep_sub_Z_ne_zero_of_delta_ne_zero
    (P Q : E.toAffine.Point)
    (hδ : delta (xRep E P) (xRep E Q) ≠ 0) :
    (xRep E (P - Q)).Z ≠ 0 := by
  classical
  cases P with
  | zero =>
      cases Q with
      | zero =>
          simp [xRep, xInf, delta] at hδ
      | some x₂ y₂ h₂ =>
          rw [show Point.zero - Point.some x₂ y₂ h₂ =
                -(Point.some x₂ y₂ h₂ : E.toAffine.Point) by rfl]
          simp [xRep, xInf, xAff, delta] at hδ ⊢
  | some x₁ y₁ h₁ =>
      cases Q with
      | zero =>
          rw [show Point.some x₁ y₁ h₁ - Point.zero =
                (Point.some x₁ y₁ h₁ : E.toAffine.Point) by rfl]
          simp [xRep, xInf, xAff, delta] at hδ ⊢
      | some x₂ y₂ h₂ =>
          have hx : x₁ ≠ x₂ := by
            intro hx
            apply hδ
            simp [xRep, xAff, delta, hx]
          simp [xRep_sub_some_of_X_ne (E := E) (h₁ := h₁) (h₂ := h₂) hx]

lemma addFromSub_not_both_zero
    (P Q : E.toAffine.Point)
    (hδ : delta (xRep E P) (xRep E Q) ≠ 0) :
    (sumNum E (xRep E P) (xRep E Q) * (xRep E (P - Q)).Z
        - (delta (xRep E P) (xRep E Q)) ^ 2 * (xRep E (P - Q)).X ≠ 0)
    ∨
    ((delta (xRep E P) (xRep E Q)) ^ 2 * (xRep E (P - Q)).Z ≠ 0) := by
  right
  exact mul_ne_zero (pow_ne_zero 2 hδ)
    (xRep_sub_Z_ne_zero_of_delta_ne_zero (E := E) P Q hδ)

set_option maxHeartbeats 2000000 in
/-- SEAM2 generalized: x-only differential addition over an arbitrary field. -/
theorem xRep_add_of_xRep_sub
    (P Q : E.toAffine.Point)
    (hδ : delta (xRep E P) (xRep E Q) ≠ 0) :
    P1.Same
      (xRep E (P + Q))
      { X := sumNum E (xRep E P) (xRep E Q) * (xRep E (P - Q)).Z
              - (delta (xRep E P) (xRep E Q)) ^ 2 * (xRep E (P - Q)).X
        Z := (delta (xRep E P) (xRep E Q)) ^ 2 * (xRep E (P - Q)).Z
        not_both_zero := addFromSub_not_both_zero (E := E) P Q hδ } := by
  classical
  have hsum := xRep_add_sub_kummer_sum (E := E) P Q
  dsimp [P1.Same]
  ring_nf at hsum ⊢
  linear_combination hsum

@[simp] lemma p1_toVec_xInf :
    P1.toVec (xInf : P1 k) = ![1, 0] := rfl

@[simp] lemma p1_toVec_xAff (x : k) :
    P1.toVec (xAff x : P1 k) = ![x, 1] := rfl

lemma xRep_toVec_eq_point_xRep (P : E.toAffine.Point) :
    P1.toVec (xRep E P) = P.xRep := by
  cases P <;> rfl

/-- Projective equality on Mathlib's `Fin 2` representatives, oriented as `v = c • u`
for a nonzero scalar `c`. This stronger orientation excludes the zero vector on the right. -/
def SameP1Vec (u v : Fin 2 → k) : Prop :=
  ∃ c : k, c ≠ 0 ∧ v = c • u

namespace SameP1Vec

lemma refl (u : Fin 2 → k) : SameP1Vec u u := by
  refine ⟨1, one_ne_zero, ?_⟩
  simp

lemma symm {u v : Fin 2 → k} (h : SameP1Vec u v) : SameP1Vec v u := by
  rcases h with ⟨c, hc, rfl⟩
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  ext i
  simp [Pi.smul_apply, hc]

lemma trans {u v w : Fin 2 → k} (huv : SameP1Vec u v) (hvw : SameP1Vec v w) :
    SameP1Vec u w := by
  rcases huv with ⟨c, hc, rfl⟩
  rcases hvw with ⟨d, hd, rfl⟩
  refine ⟨d * c, mul_ne_zero hd hc, ?_⟩
  ext i
  simp [Pi.smul_apply, mul_assoc]

lemma second_eq_zero_of_same_infty {v : Fin 2 → k}
    (h : SameP1Vec (![1, 0] : Fin 2 → k) v) : v 1 = 0 := by
  rcases h with ⟨c, _hc, rfl⟩
  simp

lemma second_ne_zero_of_same_affine {x : k} {v : Fin 2 → k}
    (h : SameP1Vec (![x, 1] : Fin 2 → k) v) : v 1 ≠ 0 := by
  rcases h with ⟨c, hc, rfl⟩
  simpa using hc

end SameP1Vec

namespace XOnly

@[simp] def X (v : Fin 2 → k) : k := v 0
@[simp] def Z (v : Fin 2 → k) : k := v 1

def xInfVec : Fin 2 → k :=
  ![1, 0]

def xAffVec (x : k) : Fin 2 → k :=
  ![x, 1]

/-- `δ = X₁Z₂ - X₂Z₁` on raw vector representatives. -/
def deltaVec (A B : Fin 2 → k) : k :=
  X A * Z B - X B * Z A

/-- Homogeneous numerator for `x₊ + x₋` on raw vector representatives. -/
def sumNumVec (A B : Fin 2 → k) : k :=
    2 * X A * X B * (X A * Z B + X B * Z A)
  + E.b₂ * X A * X B * Z A * Z B
  + E.b₄ * Z A * Z B * (X A * Z B + X B * Z A)
  + E.b₆ * Z A ^ 2 * Z B ^ 2

/-- Raw x-only differential addition: from `x(A)`, `x(B)`, and `x(A-B)`, produce `x(A+B)`.
It is deliberately unbundled because degeneracies may produce the zero vector. -/
def diffAddVec (A B D : Fin 2 → k) : Fin 2 → k :=
  let δ := deltaVec A B
  ![sumNumVec E A B * Z D - δ ^ 2 * X D, δ ^ 2 * Z D]

/-- Sequential x-only ladder: `L₀ = O`, `L₁ = P`, and
`Lₙ₊₂ = diffAdd(Lₙ₊₁, P, Lₙ)`. -/
def xLadderRep (x : k) : ℕ → Fin 2 → k
  | 0 => xInfVec
  | 1 => xAffVec x
  | n + 2 => diffAddVec E (xLadderRep x (n + 1)) (xAffVec x) (xLadderRep x n)

/-- Affine quotient readout of the x-only ladder. Meaningful when the denominator is nonzero. -/
def xLadder (x : k) (n : ℕ) : k :=
  X (xLadderRep E x n) / Z (xLadderRep E x n)

@[simp] lemma xLadderRep_zero (x : k) :
    xLadderRep E x 0 = xInfVec := rfl

@[simp] lemma xLadderRep_one (x : k) :
    xLadderRep E x 1 = xAffVec x := rfl

/-- SEAM: correctness of the total raw ladder, including degenerate differential-addition steps. -/
theorem xLadderRep_correct_seam {x y : k}
    (h : E.toAffine.Nonsingular x y) (n : ℕ) :
    SameP1Vec
      ((n • (Point.some x y h : E.toAffine.Point)).xRep)
      (xLadderRep E x n) := by
  sorry

end XOnly

/-- The intended projective x-coordinate representative `[Φₙ(x), ΨSqₙ(x)]`. -/
def xPair (W : WeierstrassCurve k) (n : ℤ) (x : k) : Fin 2 → k :=
  ![(W.Φ n).eval x, (W.ΨSq n).eval x]

/-- SEAM: the EDS/division-polynomial compatibility of the raw x-only ladder. -/
theorem xPair_same_xLadderRep_seam (W : WeierstrassCurve k) (n : ℕ) (x : k) :
    SameP1Vec
      (XOnly.xLadderRep (E := W⁄k) x n)
      (xPair W (n : ℤ) x) := by
  sorry

/-- The projective division-polynomial coordinate formula assembled from the ladder seams. -/
theorem xRep_nsmul_same_xPair (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} {x y : k} (h : (W⁄k).Nonsingular x y) :
    SameP1Vec
      ((n • (Point.some x y h : (W⁄k).Point)).xRep)
      (xPair W (n : ℤ) x) := by
  exact SameP1Vec.trans
    (XOnly.xLadderRep_correct_seam (E := W⁄k) h n)
    (xPair_same_xLadderRep_seam (W := W) n x)

/-- Keystone target reduced to the projective division-polynomial coordinate formula. -/
theorem nsmul_eq_zero_iff_ΨSq_eval (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} {x y : k} (h : (W⁄k).Nonsingular x y) :
    n • (Point.some x y h : (W⁄k).Point) = 0 ↔ (W.ΨSq (n : ℤ)).eval x = 0 := by
  classical
  let P : (W⁄k).Point := Point.some x y h
  constructor
  · intro hn
    have hsame :
        SameP1Vec ((n • P).xRep) (xPair W (n : ℤ) x) :=
      xRep_nsmul_same_xPair (W := W) (n := n) h
    have hsecond :=
      SameP1Vec.second_eq_zero_of_same_infty (v := xPair W (n : ℤ) x) (by
        simpa [P, hn] using hsame)
    simpa [xPair] using hsecond
  · intro hψ
    by_contra hn
    cases hnp : n • P with
    | zero =>
        exact hn hnp
    | some xn yn hnonsing =>
        have hsame :
            SameP1Vec ((n • P).xRep) (xPair W (n : ℤ) x) :=
          xRep_nsmul_same_xPair (W := W) (n := n) h
        have hsecond_ne :
            (xPair W (n : ℤ) x) 1 ≠ 0 :=
          SameP1Vec.second_ne_zero_of_same_affine
            (x := xn) (v := xPair W (n : ℤ) x) (by
              simpa [hnp] using hsame)
        exact hsecond_ne (by simpa [xPair] using hψ)

end KeystoneLadder
