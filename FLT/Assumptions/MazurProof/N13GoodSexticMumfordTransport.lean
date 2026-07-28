import FLT.Assumptions.MazurProof.N13GoodSexticCoordinateEquiv

/-!
# Transporting N13 Mumford graph ideals through completion of the square

The rational change of coordinates

`Y = 2y + (X³ + X + 1)`

does more than identify the two affine coordinate rings.  It sends the
generalized graph ideal `(u, y - v)` exactly to the sextic graph ideal
`(u, Y - (2v + X³ + X + 1))`.  The factor `1 / 2` appearing on the second
generator is a unit over `ℚ`, so it does not change the generated ideal.
-/

open Polynomial

namespace MazurProof.N13GoodSexticMumfordTransport

noncomputable section

open N13GoodSexticCoordinateEquiv

/-- Multiplying one generator of a two-generated ideal by a unit does not
change the ideal. -/
theorem span_pair_mul_right_unit
    {R : Type*} [CommRing R] (x a y : R) (ha : IsUnit a) :
    Ideal.span {x, a * y} = Ideal.span {x, y} := by
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact Ideal.subset_span (by simp)
    · rw [hz]
      exact Ideal.mul_mem_left _ a (Ideal.subset_span (by simp))
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact Ideal.subset_span (by simp)
    · rw [hz]
      obtain ⟨b, hab⟩ := isUnit_iff_exists_inv.mp ha
      have hba : b * a = 1 := by
        simpa [mul_comm] using hab
      have hay : a * y ∈ Ideal.span {x, a * y} :=
        Ideal.subset_span (by simp)
      have hby : b * (a * y) ∈ Ideal.span {x, a * y} :=
        Ideal.mul_mem_left _ b hay
      simpa [← mul_assoc, hba] using hby

/-- The sextic graph polynomial corresponding to a generalized graph
polynomial `v`. -/
def completedGraph (v : ℚ[X]) : ℚ[X] :=
  2 * v + N13GeneralizedMumfordIntegral.hPoly

private theorem two_mul_invTwo :
    (2 : SexticRing) *
        (algebraMap ℚ SexticRing) (2 : ℚ)⁻¹ = 1 := by
  rw [← map_ofNat (algebraMap ℚ SexticRing) 2, ← map_mul]
  norm_num

/-- Under completion of the square, the generalized graph generator is
`1 / 2` times the corresponding sextic graph generator. -/
@[simp] theorem toSextic_ySubClass (v : ℚ[X]) :
    toSextic
        (N13GeneralizedMumfordIntegral.ySubClass v) =
      (algebraMap ℚ SexticRing) (2 : ℚ)⁻¹ *
        SexticMumford.ySubClass M (completedGraph v) := by
  simp only [N13GeneralizedMumfordIntegral.ySubClass, map_sub,
    N13GoodSexticCoordinateEquiv.toSextic_yClass,
    N13GoodSexticCoordinateEquiv.toSextic_xClass,
    N13GoodSexticCoordinateEquiv.goodYInSextic,
    SexticMumford.ySubClass, completedGraph, Algebra.smul_def]
  have hhalf :
      (algebraMap ℚ SexticRing) (1 / 2 : ℚ) =
        (algebraMap ℚ SexticRing) (2 : ℚ)⁻¹ := by
    norm_num
  have hx :
      SexticMumford.xClass M
          (2 * v + N13GeneralizedMumfordIntegral.hPoly) =
        2 * SexticMumford.xClass M v +
          SexticMumford.xClass M
            N13GeneralizedMumfordIntegral.hPoly := by
    change sexticXHom
        (2 * v + N13GeneralizedMumfordIntegral.hPoly) =
      2 * sexticXHom v +
        sexticXHom N13GeneralizedMumfordIntegral.hPoly
    rw [map_add, map_mul, map_ofNat]
  rw [hhalf, hx]
  let a : SexticRing :=
    (algebraMap ℚ SexticRing) (2 : ℚ)⁻¹
  let Y : SexticRing := SexticMumford.yClass M
  let H : SexticRing :=
    SexticMumford.xClass M
      N13GeneralizedMumfordIntegral.hPoly
  let V : SexticRing :=
    SexticMumford.xClass M v
  change a * (Y - H) - V = a * (Y - (2 * V + H))
  have ha : 2 * a = 1 := two_mul_invTwo
  linear_combination V * ha

private theorem invTwo_isUnit :
    IsUnit ((algebraMap ℚ SexticRing) (2 : ℚ)⁻¹) := by
  exact
    (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ)⁻¹ ≠ 0)).map
      (algebraMap ℚ SexticRing)

/-- Completion of the square maps each generalized Mumford graph ideal
exactly onto the corresponding sextic Mumford graph ideal. -/
theorem map_mumfordIdeal (u v : ℚ[X]) :
    Ideal.map toSextic
        (N13GeneralizedMumfordIntegral.mumfordIdeal u v) =
      SexticMumford.mumfordIdeal M u (completedGraph v) := by
  rw [N13GeneralizedMumfordIntegral.mumfordIdeal,
    SexticMumford.mumfordIdeal, Ideal.map_span, Set.image_pair,
    N13GoodSexticCoordinateEquiv.toSextic_xClass,
    toSextic_ySubClass]
  exact span_pair_mul_right_unit _ _ _ invTwo_isUnit

end

end MazurProof.N13GoodSexticMumfordTransport
