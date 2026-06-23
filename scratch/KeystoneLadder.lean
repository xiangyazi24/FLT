module

public import Mathlib

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
public structure P1 (k : Type u) [Zero k] where
  X : k
  Z : k
  not_both_zero : X ≠ 0 ∨ Z ≠ 0

namespace P1

variable [Field k]

/-- Equality in `P¹`, by cross multiplication. -/
@[expose] public def Same (A B : P1 k) : Prop :=
  A.X * B.Z = B.X * A.Z

@[simp] public lemma same_refl (A : P1 k) : Same A A := by
  dsimp [Same]

@[simp] public lemma same_mk_iff {A B : P1 k} :
    Same A B ↔ A.X * B.Z = B.X * A.Z := Iff.rfl

/-- Convert the bundled nonzero `P¹` representative to Mathlib's `Fin 2` convention. -/
@[expose] public def toVec (A : P1 k) : Fin 2 → k :=
  ![A.X, A.Z]

end P1

variable (E : WeierstrassCurve k)

/-- The point at infinity on the Kummer line. -/
@[expose] public def xInf : P1 k :=
  { X := 1, Z := 0, not_both_zero := Or.inl one_ne_zero }

/-- The affine x-coordinate `[x : 1]`. -/
@[expose] public def xAff (x : k) : P1 k :=
  { X := x, Z := 1, not_both_zero := Or.inr one_ne_zero }

/-- Projective x-coordinate. The group identity maps to `[1 : 0]`. -/
@[expose] public def xRep : E.toAffine.Point → P1 k
  | 0 => xInf
  | Point.some x _ _ => xAff x

@[simp] public lemma xRep_zero :
    xRep E (0 : E.toAffine.Point) = xInf := rfl

@[simp] public lemma xRep_some {x y : k} (h : E.toAffine.Nonsingular x y) :
    xRep E (Point.some x y h : E.toAffine.Point) = xAff x := rfl

@[simp] public lemma xRep_some_X {x y : k} (h : E.toAffine.Nonsingular x y) :
    (xRep E (Point.some x y h : E.toAffine.Point)).X = x := rfl

@[simp] public lemma xRep_some_Z {x y : k} (h : E.toAffine.Nonsingular x y) :
    (xRep E (Point.some x y h : E.toAffine.Point)).Z = 1 := rfl

@[simp] public lemma xInf_X : (xInf : P1 k).X = 1 := rfl
@[simp] public lemma xInf_Z : (xInf : P1 k).Z = 0 := rfl
@[simp] public lemma xAff_X (x : k) : (xAff x).X = x := rfl
@[simp] public lemma xAff_Z (x : k) : (xAff x).Z = 1 := rfl

@[simp] public lemma xRep_neg_some_same {x y : k} (h : E.toAffine.Nonsingular x y) :
    P1.Same
      (xRep E (-(Point.some x y h : E.toAffine.Point)))
      (xRep E (Point.some x y h : E.toAffine.Point)) := by
  simp [xRep, xAff, P1.Same]

public lemma xRep_neg_same (P : E.toAffine.Point) :
    P1.Same (xRep E (-P)) (xRep E P) := by
  cases P with
  | zero =>
      rw [show -(Point.zero : E.toAffine.Point) = 0 by rfl]
      simp [xRep, xInf, P1.Same]
  | some x y h =>
      exact xRep_neg_some_same (E := E) h

/-- `δ = X₁Z₂ - X₂Z₁`. -/
@[expose] public def delta (A B : P1 k) : k :=
  A.X * B.Z - B.X * A.Z

/-- Homogeneous numerator for `x₊ + x₋`. -/
@[expose] public def sumNum (A B : P1 k) : k :=
    2 * A.X * B.X * (A.X * B.Z + B.X * A.Z)
  + E.b₂ * A.X * B.X * A.Z * B.Z
  + E.b₄ * A.Z * B.Z * (A.X * B.Z + B.X * A.Z)
  + E.b₆ * A.Z ^ 2 * B.Z ^ 2

public lemma delta_eq_zero_of_same {A B : P1 k} (h : P1.Same A B) :
    delta A B = 0 := by
  dsimp [delta, P1.Same] at h ⊢
  linear_combination h

@[simp] public lemma xRep_add_some_of_X_ne
    {x₁ y₁ x₂ y₂ : k}
    {h₁ : E.toAffine.Nonsingular x₁ y₁}
    {h₂ : E.toAffine.Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) :
    xRep E
      ((Point.some x₁ y₁ h₁ : E.toAffine.Point) + Point.some x₂ y₂ h₂)
      = xAff (E.toAffine.addX x₁ x₂ (E.toAffine.slope x₁ x₂ y₁ y₂)) := by
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (W := E.toAffine) hx]
  rfl

@[simp] public lemma xRep_sub_some_of_X_ne
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

public lemma xRep_add_sub_kummer_affine_sum_ne_x
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

public lemma some_ext_of_xy_eq
    {x₁ y₁ x₂ y₂ : k}
    {h₁ : E.toAffine.Nonsingular x₁ y₁}
    {h₂ : E.toAffine.Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : E.toAffine.Point) = Point.some x₂ y₂ h₂ := by
  subst hx
  subst hy
  congr

public lemma xRep_add_zero_of_Y_eq
    {x₁ y₁ x₂ y₂ : k}
    {h₁ : E.toAffine.Nonsingular x₁ y₁}
    {h₂ : E.toAffine.Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = E.toAffine.negY x₂ y₂) :
    xRep E ((Point.some x₁ y₁ h₁ : E.toAffine.Point) + Point.some x₂ y₂ h₂) = xInf := by
  rw [WeierstrassCurve.Affine.Point.add_of_Y_eq (W := E.toAffine) hx hy]
  rfl

public lemma xRep_sub_zero_of_same_xy
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
public theorem xRep_add_sub_kummer_sum
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

public lemma xRep_sub_Z_ne_zero_of_delta_ne_zero
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

public lemma addFromSub_not_both_zero
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
public theorem xRep_add_of_xRep_sub
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

@[simp] public lemma p1_toVec_xInf :
    P1.toVec (xInf : P1 k) = ![1, 0] := rfl

@[simp] public lemma p1_toVec_xAff (x : k) :
    P1.toVec (xAff x : P1 k) = ![x, 1] := rfl

public lemma xRep_toVec_eq_point_xRep (P : E.toAffine.Point) :
    P1.toVec (xRep E P) = P.xRep := by
  cases P <;> rfl

/-- Projective equality on Mathlib's `Fin 2` representatives, oriented as `v = c • u`
for a nonzero scalar `c`. This stronger orientation excludes the zero vector on the right. -/
@[expose] public def SameP1Vec (u v : Fin 2 → k) : Prop :=
  ∃ c : k, c ≠ 0 ∧ v = c • u

namespace SameP1Vec

public lemma mk_vec
    {u v : Fin 2 → k} {c : k}
    (hc : c ≠ 0)
    (h0 : v 0 = c * u 0)
    (h1 : v 1 = c * u 1) :
    SameP1Vec u v := by
  refine ⟨c, hc, ?_⟩
  ext i
  fin_cases i
  · simpa [Pi.smul_apply] using h0
  · simpa [Pi.smul_apply] using h1

public lemma refl (u : Fin 2 → k) : SameP1Vec u u := by
  refine ⟨1, one_ne_zero, ?_⟩
  simp

public lemma smul_right {u v : Fin 2 → k} (h : SameP1Vec u v) {c : k} (hc : c ≠ 0) :
    SameP1Vec u (c • v) := by
  rcases h with ⟨a, ha, rfl⟩
  refine ⟨c * a, mul_ne_zero hc ha, ?_⟩
  ext i
  simp [Pi.smul_apply, mul_assoc]

public lemma symm {u v : Fin 2 → k} (h : SameP1Vec u v) : SameP1Vec v u := by
  rcases h with ⟨c, hc, rfl⟩
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  ext i
  simp [Pi.smul_apply, hc]

public lemma trans {u v w : Fin 2 → k} (huv : SameP1Vec u v) (hvw : SameP1Vec v w) :
    SameP1Vec u w := by
  rcases huv with ⟨c, hc, rfl⟩
  rcases hvw with ⟨d, hd, rfl⟩
  refine ⟨d * c, mul_ne_zero hd hc, ?_⟩
  ext i
  simp [Pi.smul_apply, mul_assoc]

public lemma second_eq_zero_of_same_infty {v : Fin 2 → k}
    (h : SameP1Vec (![1, 0] : Fin 2 → k) v) : v 1 = 0 := by
  rcases h with ⟨c, _hc, rfl⟩
  simp

public lemma second_ne_zero_of_same_affine {x : k} {v : Fin 2 → k}
    (h : SameP1Vec (![x, 1] : Fin 2 → k) v) : v 1 ≠ 0 := by
  rcases h with ⟨c, hc, rfl⟩
  simpa using hc

end SameP1Vec

public lemma sameP1Vec_of_P1_same {A B : P1 k} (h : P1.Same A B) :
    SameP1Vec (P1.toVec A) (P1.toVec B) := by
  classical
  rcases A.not_both_zero with hAX | hAZ
  · refine ⟨B.X / A.X, ?_, ?_⟩
    · intro hc
      have hBX : B.X = 0 := by
        exact (div_eq_zero_iff.mp hc).resolve_right hAX
      have hBZ : B.Z = 0 := by
        have hmul : A.X * B.Z = 0 := by
          simpa [P1.Same, hBX] using h
        exact (mul_eq_zero.mp hmul).resolve_left hAX
      rcases B.not_both_zero with hBXne | hBZne
      · exact hBXne hBX
      · exact hBZne hBZ
    · ext i
      fin_cases i
      · simp [P1.toVec]
        field_simp [hAX]
      · simp [P1.toVec]
        field_simp [hAX]
        simpa [P1.Same, mul_comm] using h
  · refine ⟨B.Z / A.Z, ?_, ?_⟩
    · intro hc
      have hBZ : B.Z = 0 := by
        exact (div_eq_zero_iff.mp hc).resolve_right hAZ
      have hBX : B.X = 0 := by
        have hmul : B.X * A.Z = 0 := by
          simpa [P1.Same, hBZ] using h.symm
        exact (mul_eq_zero.mp hmul).resolve_right hAZ
      rcases B.not_both_zero with hBXne | hBZne
      · exact hBXne hBX
      · exact hBZne hBZ
    · ext i
      fin_cases i
      · simp [P1.toVec]
        field_simp [hAZ]
        simpa [P1.Same, mul_comm, mul_left_comm, mul_assoc] using h.symm
      · simp [P1.toVec]
        field_simp [hAZ]

namespace XOnly

@[expose, simp] public def X (v : Fin 2 → k) : k := v 0
@[expose, simp] public def Z (v : Fin 2 → k) : k := v 1

@[expose] public def xInfVec : Fin 2 → k :=
  ![1, 0]

@[expose] public def xAffVec (x : k) : Fin 2 → k :=
  ![x, 1]

/-- `δ = X₁Z₂ - X₂Z₁` on raw vector representatives. -/
@[expose] public def deltaVec (A B : Fin 2 → k) : k :=
  X A * Z B - X B * Z A

/-- Homogeneous numerator for `x₊ + x₋` on raw vector representatives. -/
@[expose] public def sumNumVec (A B : Fin 2 → k) : k :=
    2 * X A * X B * (X A * Z B + X B * Z A)
  + E.b₂ * X A * X B * Z A * Z B
  + E.b₄ * Z A * Z B * (X A * Z B + X B * Z A)
  + E.b₆ * Z A ^ 2 * Z B ^ 2

/-- Raw x-only differential addition: from `x(A)`, `x(B)`, and `x(A-B)`, produce `x(A+B)`.
It is deliberately unbundled because degeneracies may produce the zero vector. -/
@[expose] public def diffAddVec (A B D : Fin 2 → k) : Fin 2 → k :=
  let δ := deltaVec A B
  ![sumNumVec E A B * Z D - δ ^ 2 * X D, δ ^ 2 * Z D]

/-- Homogeneous numerator for the x-coordinate doubling map. -/
@[expose] public def dupNumH (X Z : k) : k :=
  X ^ 4 - E.b₄ * X ^ 2 * Z ^ 2 - 2 * E.b₆ * X * Z ^ 3 - E.b₈ * Z ^ 4

/-- Homogeneous denominator for the x-coordinate doubling map. -/
@[expose] public def dupDenH (X Z : k) : k :=
  4 * X ^ 3 * Z + E.b₂ * X ^ 2 * Z ^ 2 + 2 * E.b₄ * X * Z ^ 3 + E.b₆ * Z ^ 4

/-- Raw x-only doubling primitive. -/
@[expose] public def doubleVec (A : Fin 2 → k) : Fin 2 → k :=
  ![dupNumH E (X A) (Z A), dupDenH E (X A) (Z A)]

/-- Differential addition with the adjacent-pair degenerate branch made total.
For a genuine adjacent ladder pair, `δ = 0` means the desired sum is the point at infinity. -/
@[expose] public def diffAddOrInfVec (A B D : Fin 2 → k) : Fin 2 → k :=
  if deltaVec A B = 0 then xInfVec else diffAddVec E A B D

public lemma deltaVec_smul_smul (A B : Fin 2 → k) (a b : k) :
    deltaVec (a • A) (b • B) = a * b * deltaVec A B := by
  simp [deltaVec, X, Z, Pi.smul_apply]
  ring

public lemma sumNumVec_smul_smul (A B : Fin 2 → k) (a b : k) :
    sumNumVec E (a • A) (b • B) = a ^ 2 * b ^ 2 * sumNumVec E A B := by
  simp [sumNumVec, X, Z, Pi.smul_apply]
  ring

public lemma diffAddVec_smul_smul_smul (A B D : Fin 2 → k) (a b d : k) :
    diffAddVec E (a • A) (b • B) (d • D) =
      (a ^ 2 * b ^ 2 * d) • diffAddVec E A B D := by
  ext i <;> fin_cases i
  · simp [diffAddVec, sumNumVec_smul_smul, deltaVec_smul_smul, X, Z, Pi.smul_apply]
    ring
  · simp [diffAddVec, deltaVec_smul_smul, X, Z, Pi.smul_apply]
    ring

public lemma diffAddVec_congr
    {A A' B B' D D' : Fin 2 → k}
    (hA : SameP1Vec A A') (hB : SameP1Vec B B') (hD : SameP1Vec D D') :
    SameP1Vec (diffAddVec E A B D) (diffAddVec E A' B' D') := by
  rcases hA with ⟨a, ha, rfl⟩
  rcases hB with ⟨b, hb, rfl⟩
  rcases hD with ⟨d, hd, rfl⟩
  refine ⟨a ^ 2 * b ^ 2 * d,
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 hb)) hd, ?_⟩
  exact diffAddVec_smul_smul_smul (E := E) A B D a b d

public lemma diffAddOrInfVec_congr
    {A A' B B' D D' : Fin 2 → k}
    (hA : SameP1Vec A A') (hB : SameP1Vec B B') (hD : SameP1Vec D D') :
    SameP1Vec (diffAddOrInfVec E A B D) (diffAddOrInfVec E A' B' D') := by
  classical
  rcases hA with ⟨a, ha, rfl⟩
  rcases hB with ⟨b, hb, rfl⟩
  rcases hD with ⟨d, hd, rfl⟩
  unfold diffAddOrInfVec
  by_cases hδ : deltaVec A B = 0
  · have hδ' : deltaVec (a • A) (b • B) = 0 := by
      simp [deltaVec_smul_smul, hδ]
    simp [hδ, hδ', SameP1Vec.refl]
  · have hδ' : deltaVec (a • A) (b • B) ≠ 0 := by
      simpa [deltaVec_smul_smul] using mul_ne_zero (mul_ne_zero ha hb) hδ
    simp [hδ, hδ']
    refine ⟨a ^ 2 * b ^ 2 * d,
      mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 hb)) hd, ?_⟩
    exact diffAddVec_smul_smul_smul (E := E) A B D a b d

public lemma dupNumH_smul (A : Fin 2 → k) (c : k) :
    dupNumH E (X (c • A)) (Z (c • A)) = c ^ 4 * dupNumH E (X A) (Z A) := by
  simp [dupNumH, X, Z, Pi.smul_apply]
  ring

public lemma dupDenH_smul (A : Fin 2 → k) (c : k) :
    dupDenH E (X (c • A)) (Z (c • A)) = c ^ 4 * dupDenH E (X A) (Z A) := by
  simp [dupDenH, X, Z, Pi.smul_apply]
  ring

public lemma doubleVec_congr {A B : Fin 2 → k} (h : SameP1Vec A B) :
    SameP1Vec (doubleVec E A) (doubleVec E B) := by
  rcases h with ⟨c, hc, rfl⟩
  refine ⟨c ^ 4, pow_ne_zero 4 hc, ?_⟩
  ext i <;> fin_cases i
  · simpa [doubleVec, X, Z, Pi.smul_apply] using dupNumH_smul (E := E) A c
  · simpa [doubleVec, X, Z, Pi.smul_apply] using dupDenH_smul (E := E) A c

private lemma dupDenH_eq_Yder_sq
    {x y : k} (hE : E.toAffine.Equation x y) :
    dupDenH E x 1 = (y - E.toAffine.negY x y) ^ 2 := by
  have hE0 : y ^ 2 + E.a₁ * x * y + E.a₃ * y -
      (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆) = 0 := by
    simpa [Affine.equation_iff'] using hE
  rw [dupDenH, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, Affine.negY]
  linear_combination (norm := ring1) -4 * hE0

private lemma dupNumH_eq_polynomialX_sq_of_Yder_zero
    {x y : k} (hE : E.toAffine.Equation x y)
    (hY : y - E.toAffine.negY x y = 0) :
    dupNumH E x 1 =
      (E.a₁ * y - (3 * x ^ 2 + 2 * E.a₂ * x + E.a₄)) ^ 2 := by
  have hE0 : y ^ 2 + E.a₁ * x * y + E.a₃ * y -
      (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆) = 0 := by
    simpa [Affine.equation_iff'] using hE
  have hY0 : 2 * y + E.a₁ * x + E.a₃ = 0 := by
    rw [Affine.negY] at hY
    linear_combination (norm := ring1) hY
  rw [dupNumH, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  linear_combination (norm := ring1)
      (E.a₁ ^ 2 + 4 * E.a₂ + 8 * x) * hE0
    + (-(E.a₁ ^ 2) * y + E.a₁ * E.a₂ * x + E.a₁ * E.a₄
        + E.a₁ * x ^ 2 - E.a₂ * E.a₃ - 2 * E.a₂ * y
        - 2 * E.a₃ * x - 4 * x * y) * hY0

private lemma dupNumH_eq_dupDenH_mul_addX_of_Yder_ne
    {x y : k} (hE : E.toAffine.Equation x y)
    (hy : y ≠ E.toAffine.negY x y) :
    dupNumH E x 1 =
      dupDenH E x 1 * E.toAffine.addX x x (E.toAffine.slope x x y y) := by
  have hE0 : y ^ 2 + E.a₁ * x * y + E.a₃ * y -
      (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆) = 0 := by
    simpa [Affine.equation_iff'] using hE
  have hden : y - E.toAffine.negY x y ≠ 0 := sub_ne_zero.mpr hy
  rw [dupNumH, dupDenH, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, Affine.addX]
  rw [Affine.slope_of_Y_ne (W := E.toAffine) rfl hy]
  field_simp [hden]
  rw [Affine.negY]
  linear_combination (norm := ring1)
    (E.a₁ ^ 2 * x + E.a₁ * E.a₃ + 4 * E.a₂ * x
      + 2 * E.a₄ + 6 * x ^ 2) ^ 2 * hE0

private lemma dupNumH_ne_zero_of_Yder_zero
    {x y : k} (h : E.toAffine.Nonsingular x y)
    (hY : y - E.toAffine.negY x y = 0) :
    dupNumH E x 1 ≠ 0 := by
  have hYpoly : (E.toAffine.polynomialY).evalEval x y = 0 := by
    rw [Affine.evalEval_polynomialY]
    rw [Affine.negY] at hY
    linear_combination (norm := ring1) hY
  have hXpoly : (E.toAffine.polynomialX).evalEval x y ≠ 0 :=
    h.2.resolve_right (by simpa [hYpoly])
  have hX :
      E.a₁ * y - (3 * x ^ 2 + 2 * E.a₂ * x + E.a₄) ≠ 0 := by
    simpa [Affine.evalEval_polynomialX] using hXpoly
  have hN := dupNumH_eq_polynomialX_sq_of_Yder_zero (E := E) h.1 hY
  rw [hN]
  exact pow_ne_zero 2 hX

private theorem xRep_two_nsmul_same_dup_affine
    (P : E.toAffine.Point) :
    SameP1Vec ((2 • P).xRep) (doubleVec E P.xRep) := by
  classical
  rcases P with _ | ⟨x, y, h⟩
  · refine SameP1Vec.mk_vec
      (u := ((2 • (0 : E.toAffine.Point)).xRep))
      (v := doubleVec E ((0 : E.toAffine.Point).xRep))
      (c := 1) one_ne_zero ?_ ?_
    · simp [doubleVec, dupNumH]
    · simp [doubleVec, dupDenH]
  · by_cases hy : y = E.toAffine.negY x y
    · have hY : y - E.toAffine.negY x y = 0 := sub_eq_zero.mpr hy
      have htwo :
          2 • (Point.some x y h : E.toAffine.Point) = 0 := by
        simpa [two_nsmul] using
          (Point.add_self_of_Y_eq (W := E.toAffine) (h₁ := h) hy)
      have hD0 : dupDenH E x 1 = 0 := by
        rw [dupDenH_eq_Yder_sq (E := E) h.1, hY]
        norm_num
      have hN0 : dupNumH E x 1 ≠ 0 :=
        dupNumH_ne_zero_of_Yder_zero (E := E) h hY
      refine SameP1Vec.mk_vec
        (u := ((2 • (Point.some x y h : E.toAffine.Point)).xRep))
        (v := doubleVec E ((Point.some x y h : E.toAffine.Point).xRep))
        (c := dupNumH E x 1) hN0 ?_ ?_
      · simp [htwo, doubleVec]
      · simp [htwo, hD0, doubleVec]
    · have hYne : y - E.toAffine.negY x y ≠ 0 := sub_ne_zero.mpr hy
      have hD_eq : dupDenH E x 1 = (y - E.toAffine.negY x y) ^ 2 :=
        dupDenH_eq_Yder_sq (E := E) h.1
      have hDne : dupDenH E x 1 ≠ 0 := by
        rw [hD_eq]
        exact pow_ne_zero 2 hYne
      have htwo :
          2 • (Point.some x y h : E.toAffine.Point) =
            Point.some _ _ (Affine.nonsingular_add h h (fun hxy => hy hxy.right)) := by
        simpa [two_nsmul] using
          (Point.add_self_of_Y_ne (W := E.toAffine) (h₁ := h) hy)
      have hN :
          dupNumH E x 1 =
            dupDenH E x 1 * E.toAffine.addX x x (E.toAffine.slope x x y y) :=
        dupNumH_eq_dupDenH_mul_addX_of_Yder_ne (E := E) h.1 hy
      refine SameP1Vec.mk_vec
        (u := ((2 • (Point.some x y h : E.toAffine.Point)).xRep))
        (v := doubleVec E ((Point.some x y h : E.toAffine.Point).xRep))
        (c := dupDenH E x 1) hDne ?_ ?_
      · simp [htwo, hN, doubleVec]
      · simp [htwo, doubleVec]

/-- Montgomery-pair ladder state: the first component represents `x(mP)` and the second
represents `x((m+1)P)`. -/
@[expose] public def xLadderPair (x : k) : ℕ → (Fin 2 → k) × (Fin 2 → k)
  | 0 => (xInfVec, xAffVec x)
  | 1 => (xAffVec x, doubleVec E (xAffVec x))
  | n + 2 =>
      let N := n + 2
      let S := xLadderPair x (N / 2)
      let A := S.1
      let B := S.2
      let C := diffAddOrInfVec E A B (xAffVec x)
      if Even N then (doubleVec E A, C) else (C, doubleVec E B)
termination_by n => n
decreasing_by
  omega

/-- The x-only ladder representative for `x(nP)`, extracted from the Montgomery pair state. -/
@[expose] public def xLadderRep (x : k) (n : ℕ) : Fin 2 → k :=
  (xLadderPair E x n).1

/-- Affine quotient readout of the x-only ladder. Meaningful when the denominator is nonzero. -/
@[expose] public def xLadder (x : k) (n : ℕ) : k :=
  X (xLadderRep E x n) / Z (xLadderRep E x n)

@[simp] public lemma xLadderRep_zero (x : k) :
    xLadderRep E x 0 = xInfVec := by
  simp [xLadderRep, xLadderPair]

@[simp] public lemma xLadderRep_one (x : k) :
    xLadderRep E x 1 = xAffVec x := by
  simp [xLadderRep, xLadderPair]

@[simp] public lemma xLadderRep_two (x : k) :
    xLadderRep E x 2 = doubleVec E (xAffVec x) := by
  simp [xLadderRep, xLadderPair]

@[simp] public lemma xLadderRep_three (x : k) :
    xLadderRep E x 3 =
      diffAddOrInfVec E (xAffVec x) (doubleVec E (xAffVec x)) (xAffVec x) := by
  simp [xLadderRep, xLadderPair, show ¬ Even (3 : ℕ) by decide]

@[simp] public lemma xLadderRep_four (x : k) :
    xLadderRep E x 4 = doubleVec E (doubleVec E (xAffVec x)) := by
  simp [xLadderRep, xLadderPair, show Even (4 : ℕ) by decide]

public lemma deltaVec_point_xRep_eq (P Q : E.toAffine.Point) :
    deltaVec P.xRep Q.xRep = delta (xRep E P) (xRep E Q) := by
  cases P <;> cases Q <;>
    simp [deltaVec, delta, xRep, xInf, xAff, X, Z, Affine.Point.xRep]

@[simp] public lemma xRep_X_eq_point_xRep_zero (P : E.toAffine.Point) :
    (xRep E P).X = P.xRep 0 := by
  cases P <;> rfl

@[simp] public lemma xRep_Z_eq_point_xRep_one (P : E.toAffine.Point) :
    (xRep E P).Z = P.xRep 1 := by
  cases P <;> rfl

public lemma xRep_add_of_xRep_sub_vec
    (P Q : E.toAffine.Point)
    (hδ : deltaVec P.xRep Q.xRep ≠ 0) :
    SameP1Vec
      ((P + Q).xRep)
      (diffAddVec E P.xRep Q.xRep (P - Q).xRep) := by
  have hδ' : delta (xRep E P) (xRep E Q) ≠ 0 := by
    simpa [deltaVec_point_xRep_eq (E := E) P Q] using hδ
  have hsame := xRep_add_of_xRep_sub (E := E) P Q hδ'
  have hvec := sameP1Vec_of_P1_same hsame
  rw [xRep_toVec_eq_point_xRep (E := E) (P + Q)] at hvec
  simpa [P1.toVec, diffAddVec, deltaVec, delta, sumNumVec, sumNum, X, Z,
    xRep_toVec_eq_point_xRep, xRep_X_eq_point_xRep_zero, xRep_Z_eq_point_xRep_one] using hvec

public lemma point_xRep_eq_of_deltaVec_zero
    (P Q : E.toAffine.Point)
    (hδ : deltaVec P.xRep Q.xRep = 0) :
    P.xRep = Q.xRep := by
  cases P with
  | zero =>
      cases Q with
      | zero => rfl
      | some x y h =>
          simp [deltaVec, X, Z, Affine.Point.xRep] at hδ
  | some x₁ y₁ h₁ =>
      cases Q with
      | zero =>
          simp [deltaVec, X, Z, Affine.Point.xRep] at hδ
      | some x₂ y₂ h₂ =>
          have hx : x₁ = x₂ :=
            sub_eq_zero.mp (by simpa [deltaVec, X, Z, Affine.Point.xRep] using hδ)
          ext i
          fin_cases i
          · simpa [hx]
          · simp

public lemma deltaVec_eq_zero_of_scaled
    {U V A B : Fin 2 → k}
    (hA : SameP1Vec U A) (hB : SameP1Vec V B)
    (hδ : deltaVec A B = 0) :
    deltaVec U V = 0 := by
  rcases hA with ⟨a, ha, rfl⟩
  rcases hB with ⟨b, hb, rfl⟩
  have hscaled : a * b * deltaVec U V = 0 := by
    simpa [deltaVec_smul_smul] using hδ
  exact (mul_eq_zero.mp hscaled).resolve_left (mul_ne_zero ha hb)

public lemma deltaVec_ne_zero_of_scaled
    {U V A B : Fin 2 → k}
    (hA : SameP1Vec U A) (hB : SameP1Vec V B)
    (hδ : deltaVec A B ≠ 0) :
    deltaVec U V ≠ 0 := by
  rcases hA with ⟨a, ha, rfl⟩
  rcases hB with ⟨b, hb, rfl⟩
  intro hzero
  apply hδ
  simp [deltaVec_smul_smul, hzero]

private lemma adjacent_sub_nsmul {G : Type*} [AddCommGroup G] (P : G) (m : ℕ) :
    ((m + 1) • P) - (m • P) = P := by
  rw [succ_nsmul]
  abel

private lemma adjacent_sub_nsmul_rev {G : Type*} [AddCommGroup G] (P : G) (m : ℕ) :
    (m • P) - ((m + 1) • P) = -P := by
  rw [succ_nsmul]
  abel

private lemma adjacent_add_nsmul {G : Type*} [AddCommGroup G] (P : G) (m : ℕ) :
    ((m + 1) • P) + (m • P) = (2 * m + 1) • P := by
  calc
    ((m + 1) • P) + (m • P) = ((m + 1) + m) • P := by
      symm
      rw [add_nsmul]
    _ = (2 * m + 1) • P := by
      congr 1
      omega

private lemma double_nsmul {G : Type*} [AddCommGroup G] (P : G) (m : ℕ) :
    2 • (m • P) = (2 * m) • P := by
  rw [show 2 * m = m * 2 by omega]
  rw [mul_nsmul]

private lemma double_succ_nsmul {G : Type*} [AddCommGroup G] (P : G) (m : ℕ) :
    2 • ((m + 1) • P) = (2 * m + 2) • P := by
  rw [show 2 * m + 2 = (m + 1) * 2 by omega]
  rw [mul_nsmul]

private lemma odd_nsmul_eq_zero_of_adjacent_delta_zero
    (P : E.toAffine.Point) (hP : P ≠ 0) (m : ℕ)
    (hδ : deltaVec (m • P).xRep ((m + 1) • P).xRep = 0) :
    (2 * m + 1) • P = 0 := by
  have hxrep :
      (m • P).xRep = ((m + 1) • P).xRep :=
    point_xRep_eq_of_deltaVec_zero (E := E) (m • P) ((m + 1) • P) hδ
  rcases Point.xRep_eq_xRep_iff.mp hxrep with hsame | hneg
  · have hsub0 : ((m + 1) • P) - (m • P) = 0 := by
      rw [← hsame, sub_self]
    have hp0 : P = 0 := by
      simpa [adjacent_sub_nsmul] using hsub0
    exact (hP hp0).elim
  · have hsum0 : ((m + 1) • P) + (m • P) = 0 := by
      rw [hneg, add_neg_cancel]
    simpa [adjacent_add_nsmul] using hsum0

private lemma diffAddOrInfVec_adjacent_correct
    (P : E.toAffine.Point) (hP : P ≠ 0) (m : ℕ)
    {A B D : Fin 2 → k}
    (hA : SameP1Vec (m • P).xRep A)
    (hB : SameP1Vec ((m + 1) • P).xRep B)
    (hD : SameP1Vec P.xRep D) :
    SameP1Vec
      (((2 * m + 1) • P).xRep)
      (diffAddOrInfVec E A B D) := by
  classical
  unfold diffAddOrInfVec
  by_cases hδ : deltaVec A B = 0
  · simp [hδ]
    have hδexact :
        deltaVec (m • P).xRep ((m + 1) • P).xRep = 0 :=
      deltaVec_eq_zero_of_scaled hA hB hδ
    have hzero := odd_nsmul_eq_zero_of_adjacent_delta_zero (E := E) P hP m hδexact
    simpa [hzero, xInfVec] using SameP1Vec.refl (xInfVec : Fin 2 → k)
  · simp [hδ]
    have hδexact :
        deltaVec (m • P).xRep ((m + 1) • P).xRep ≠ 0 :=
      deltaVec_ne_zero_of_scaled hA hB hδ
    have hgeom :=
      xRep_add_of_xRep_sub_vec (E := E) (m • P) ((m + 1) • P) hδexact
    have hadd :
        (m • P) + ((m + 1) • P) = (2 * m + 1) • P := by
      rw [add_comm]
      exact adjacent_add_nsmul P m
    have hgeom' :
        SameP1Vec (((2 * m + 1) • P).xRep)
          (diffAddVec E (m • P).xRep ((m + 1) • P).xRep
            ((m • P) - ((m + 1) • P)).xRep) := by
      simpa [hadd] using hgeom
    have hDsub :
        SameP1Vec (((m • P) - ((m + 1) • P)).xRep) D := by
      have hsub : (m • P) - ((m + 1) • P) = -P :=
        adjacent_sub_nsmul_rev P m
      have hsameNeg : SameP1Vec (((m • P) - ((m + 1) • P)).xRep) P.xRep := by
        rw [hsub, Point.xRep_neg]
        exact SameP1Vec.refl P.xRep
      exact SameP1Vec.trans hsameNeg hD
    exact SameP1Vec.trans hgeom'
      (diffAddVec_congr (E := E) hA hB hDsub)

/-- SEAM: correctness of the total raw ladder, including degenerate differential-addition steps. -/
public theorem xLadderRep_correct_seam {x y : k}
    (h : E.toAffine.Nonsingular x y) (n : ℕ) :
    SameP1Vec
      ((n • (Point.some x y h : E.toAffine.Point)).xRep)
      (xLadderRep E x n) := by
  classical
  let P : E.toAffine.Point := Point.some x y h
  have hPne : P ≠ 0 := by
    simp [P]
  have hD : SameP1Vec P.xRep (xAffVec x) := by
    simpa [P, xAffVec] using SameP1Vec.refl P.xRep
  have hpair :
      ∀ n : ℕ,
        SameP1Vec ((n • P).xRep) (xLadderPair E x n).1 ∧
        SameP1Vec (((n + 1) • P).xRep) (xLadderPair E x n).2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n IH =>
        rcases n with _ | n
        · constructor
          · simpa [xLadderPair, P, xInfVec] using
              SameP1Vec.refl ((0 : E.toAffine.Point).xRep)
          · simpa [xLadderPair, P, xAffVec] using
              SameP1Vec.refl P.xRep
        · rcases n with _ | n
          · constructor
            · simpa [xLadderPair, P, xAffVec] using
                SameP1Vec.refl P.xRep
            · have hdup := xRep_two_nsmul_same_dup_affine (E := E) P
              simpa [xLadderPair, P, xAffVec, doubleVec] using hdup
          · let N : ℕ := n + 2
            let m : ℕ := N / 2
            have hm_lt : m < N := by
              dsimp [m, N]
              omega
            have IHm := IH m (by
              dsimp [m, N]
              omega)
            have hadd :
                SameP1Vec (((2 * m + 1) • P).xRep)
                  (diffAddOrInfVec E (xLadderPair E x m).1 (xLadderPair E x m).2
                    (xAffVec x)) :=
              diffAddOrInfVec_adjacent_correct (E := E) P hPne m IHm.1 IHm.2 hD
            have hdouble₀ :
                SameP1Vec (((2 * m) • P).xRep)
                  (doubleVec E (xLadderPair E x m).1) := by
              have hraw := xRep_two_nsmul_same_dup_affine (E := E) (m • P)
              have hscaled := doubleVec_congr (E := E) IHm.1
              have htrans := SameP1Vec.trans hraw hscaled
              simpa [double_nsmul] using htrans
            have hdouble₁ :
                SameP1Vec (((2 * m + 2) • P).xRep)
                  (doubleVec E (xLadderPair E x m).2) := by
              have hraw := xRep_two_nsmul_same_dup_affine (E := E) ((m + 1) • P)
              have hscaled := doubleVec_congr (E := E) IHm.2
              have htrans := SameP1Vec.trans hraw hscaled
              simpa [double_succ_nsmul] using htrans
            by_cases hEven : Even N
            · have hN : N = 2 * m := by
                simpa [m] using (Nat.two_mul_div_two_of_even hEven).symm
              have hN1 : N + 1 = 2 * m + 1 := by omega
              constructor
              · have hfirst :
                    SameP1Vec ((N • P).xRep)
                      (doubleVec E (xLadderPair E x m).1) := by
                  simpa [hN] using hdouble₀
                simpa [xLadderPair, N, m, hEven] using hfirst
              · have hsecond :
                    SameP1Vec (((N + 1) • P).xRep)
                      (diffAddOrInfVec E (xLadderPair E x m).1 (xLadderPair E x m).2
                        (xAffVec x)) := by
                  simpa [hN1] using hadd
                simpa [xLadderPair, N, m, hEven] using hsecond
            · have hOdd : Odd N := Nat.not_even_iff_odd.mp hEven
              have hN : N = 2 * m + 1 := by
                simpa [m] using (Nat.two_mul_div_two_add_one_of_odd hOdd).symm
              have hN1 : N + 1 = 2 * m + 2 := by omega
              constructor
              · have hfirst :
                    SameP1Vec ((N • P).xRep)
                      (diffAddOrInfVec E (xLadderPair E x m).1 (xLadderPair E x m).2
                        (xAffVec x)) := by
                  simpa [hN] using hadd
                simpa [xLadderPair, N, m, hEven] using hfirst
              · have hsecond :
                    SameP1Vec (((N + 1) • P).xRep)
                      (doubleVec E (xLadderPair E x m).2) := by
                  simpa [hN1] using hdouble₁
                simpa [xLadderPair, N, m, hEven] using hsecond
  simpa [xLadderRep, P] using (hpair n).1

public lemma xLadderRep_ne_zero_of_nonsingular {x y : k}
    (h : E.toAffine.Nonsingular x y) (n : ℕ) :
    xLadderRep E x n ≠ 0 := by
  classical
  let P : E.toAffine.Point := Point.some x y h
  have hsame := xLadderRep_correct_seam (E := E) h n
  rcases hsame with ⟨c, hc, hrep⟩
  rw [hrep]
  intro hzero
  exact Affine.Point.xRep_ne_zero (n • P)
    ((smul_eq_zero.mp hzero).resolve_left hc)

public lemma xLadderRep_two_ne_zero_of_nonsingular {x y : k}
    (h : E.toAffine.Nonsingular x y) :
    xLadderRep E x 2 ≠ 0 :=
  xLadderRep_ne_zero_of_nonsingular (E := E) h 2

public lemma xLadderRep_three_ne_zero_of_nonsingular {x y : k}
    (h : E.toAffine.Nonsingular x y) :
    xLadderRep E x 3 ≠ 0 :=
  xLadderRep_ne_zero_of_nonsingular (E := E) h 3

public lemma xLadderRep_four_ne_zero_of_nonsingular {x y : k}
    (h : E.toAffine.Nonsingular x y) :
    xLadderRep E x 4 ≠ 0 :=
  xLadderRep_ne_zero_of_nonsingular (E := E) h 4

end XOnly

/-- The intended projective x-coordinate representative `[Φₙ(x), ΨSqₙ(x)]`. -/
@[expose] public def xPair (W : WeierstrassCurve k) (n : ℤ) (x : k) : Fin 2 → k :=
  ![(W.Φ n).eval x, (W.ΨSq n).eval x]

/-- Sanity check: the EDS representative agrees with the ladder at `n = 0`. -/
public theorem xPair_same_xLadderRep_zero (W : WeierstrassCurve k) (x : k) :
    SameP1Vec
      (XOnly.xLadderRep (E := W⁄k) x 0)
      (xPair W (0 : ℤ) x) := by
  simpa [xPair, XOnly.xInfVec] using SameP1Vec.refl (![1, 0] : Fin 2 → k)

/-- Sanity check: the EDS representative agrees with the ladder at `n = 1`. -/
public theorem xPair_same_xLadderRep_one (W : WeierstrassCurve k) (x : k) :
    SameP1Vec
      (XOnly.xLadderRep (E := W⁄k) x 1)
      (xPair W (1 : ℤ) x) := by
  simpa [xPair, XOnly.xAffVec] using SameP1Vec.refl (![x, 1] : Fin 2 → k)

/-- Sanity check: the EDS representative agrees with the ladder at `n = 2`. -/
public theorem xPair_same_xLadderRep_two (W : WeierstrassCurve k) (x : k) :
    SameP1Vec
      (XOnly.xLadderRep (E := W⁄k) x 2)
      (xPair W (2 : ℤ) x) := by
  simpa [xPair, XOnly.doubleVec, XOnly.dupNumH, XOnly.dupDenH, XOnly.xAffVec,
    WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.baseChange]
    using SameP1Vec.refl (XOnly.doubleVec (E := W⁄k) (XOnly.xAffVec x))

end KeystoneLadder
