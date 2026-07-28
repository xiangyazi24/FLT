import FLT.Assumptions.MazurProof.N13GeneralizedMumfordIntegral
import FLT.Assumptions.MazurProof.N13Mumford

/-!
# Completing the square on the N13 coordinate rings

Over `ℚ`, the good generalized equation

`y² + (X³+X+1)y = X⁵+X⁴`

and the sextic equation already used by the concrete Picard group are
isomorphic by

`Y = 2y + (X³+X+1)`.

This file constructs that isomorphism directly from the two `AdjoinRoot`
presentations and records its action on both coordinates.  It is the
algebraic bridge needed to interpret integral generalized Mumford graph
ideals as classes in the existing oriented sextic Picard group.
-/

open Polynomial

namespace MazurProof.N13GoodSexticCoordinateEquiv

noncomputable section

abbrev M : SexticMumford.Model ℚ :=
  N13Mumford.model ℚ

abbrev GoodRing : Type :=
  N13GeneralizedMumfordIntegral.CoordinateRing (R := ℚ)

abbrev SexticRing : Type :=
  N13Mumford.CoordinateRing ℚ

def goodXHom : ℚ[X] →+* GoodRing :=
  N13GeneralizedMumfordIntegral.xClassHom

def sexticXHom : ℚ[X] →+* SexticRing :=
  AdjoinRoot.of (SexticMumford.curvePoly M)

@[simp] theorem goodXHom_apply (p : ℚ[X]) :
    goodXHom p =
      N13GeneralizedMumfordIntegral.xClass p := rfl

@[simp] theorem sexticXHom_apply (p : ℚ[X]) :
    sexticXHom p = SexticMumford.xClass M p := rfl

abbrev hPoly : ℚ[X] :=
  N13GeneralizedMumfordIntegral.hPoly

abbrev rhsPoly : ℚ[X] :=
  N13GeneralizedMumfordIntegral.rhsPoly

/-- The polynomial identity behind completion of the square. -/
theorem sextic_eq_h_sq_add_four_rhs :
    N13Mumford.f ℚ = hPoly ^ 2 + 4 * rhsPoly := by
  simp only [N13Mumford.f, hPoly, rhsPoly,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GeneralizedMumfordIntegral.rhsPoly]
  ring

/-- The good `y` coordinate inside the sextic coordinate ring. -/
def goodYInSextic : SexticRing :=
  (1 / 2 : ℚ) •
    (SexticMumford.yClass M - sexticXHom hPoly)

/-- The sextic `Y` coordinate inside the good coordinate ring. -/
def sexticYInGood : GoodRing :=
  2 * N13GeneralizedMumfordIntegral.yClass +
    goodXHom hPoly

private theorem goodYInSextic_root :
    N13GeneralizedMumfordIntegral.curvePoly.eval₂
      sexticXHom goodYInSextic = 0 := by
  simp only [N13GeneralizedMumfordIntegral.curvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C,
    eval₂_mul]
  have hy := SexticMumford.yClass_sq M
  change
    SexticMumford.yClass M ^ 2 =
      sexticXHom (N13Mumford.f ℚ) at hy
  rw [sextic_eq_h_sq_add_four_rhs] at hy
  simp only [map_add, map_mul, map_pow, map_ofNat] at hy
  let a : SexticRing :=
    (algebraMap ℚ SexticRing) (1 / 2)
  let Y : SexticRing := SexticMumford.yClass M
  let H : SexticRing := sexticXHom hPoly
  let R : SexticRing := sexticXHom rhsPoly
  simp only [goodYInSextic, Algebra.smul_def]
  change (a * (Y - H)) ^ 2 + H * (a * (Y - H)) - R = 0
  have hy' : Y ^ 2 = H ^ 2 + 4 * R := hy
  have ha : 2 * a = 1 := by
    dsimp only [a]
    rw [← map_ofNat (algebraMap ℚ SexticRing) 2,
      ← map_mul]
    norm_num
  linear_combination
    a ^ 2 * hy' +
      (-a * Y * H + a * H ^ 2 + (2 * a + 1) * R) * ha

private theorem good_root_relation :
    N13GeneralizedMumfordIntegral.yClass ^ 2 +
        goodXHom hPoly *
          N13GeneralizedMumfordIntegral.yClass -
      goodXHom rhsPoly = 0 := by
  apply sub_eq_zero.mpr
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [N13GeneralizedMumfordIntegral.curvePoly]
  ring

private theorem sexticYInGood_root :
    (SexticMumford.curvePoly M).eval₂
      goodXHom sexticYInGood = 0 := by
  simp only [SexticMumford.curvePoly,
    eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  change
    sexticYInGood ^ 2 -
      goodXHom (N13Mumford.f ℚ) = 0
  rw [sextic_eq_h_sq_add_four_rhs]
  simp only [map_add, map_mul, map_pow, map_ofNat]
  unfold sexticYInGood
  linear_combination 4 * good_root_relation

/-- Completion of the square as a ring homomorphism from the good model to
the sextic model. -/
def toSextic : GoodRing →+* SexticRing :=
  AdjoinRoot.lift sexticXHom goodYInSextic
    goodYInSextic_root

/-- The inverse change of variables. -/
def toGood : SexticRing →+* GoodRing :=
  AdjoinRoot.lift goodXHom sexticYInGood
    sexticYInGood_root

@[simp] theorem toSextic_xClass (p : ℚ[X]) :
    toSextic
        (N13GeneralizedMumfordIntegral.xClass p) =
      SexticMumford.xClass M p := by
  change
    toSextic
        (AdjoinRoot.of
          (N13GeneralizedMumfordIntegral.curvePoly (R := ℚ)) p) =
      sexticXHom p
  exact AdjoinRoot.lift_of goodYInSextic_root

@[simp] theorem toSextic_yClass :
    toSextic
        N13GeneralizedMumfordIntegral.yClass =
      goodYInSextic :=
  AdjoinRoot.lift_root goodYInSextic_root

@[simp] theorem toGood_xClass (p : ℚ[X]) :
    toGood (SexticMumford.xClass M p) =
      N13GeneralizedMumfordIntegral.xClass p := by
  change
    toGood
        (AdjoinRoot.of
          (SexticMumford.curvePoly M) p) =
      goodXHom p
  exact AdjoinRoot.lift_of sexticYInGood_root

@[simp] theorem toGood_yClass :
    toGood (SexticMumford.yClass M) =
      sexticYInGood :=
  AdjoinRoot.lift_root sexticYInGood_root

private theorem invTwo_mul_two_good :
    (algebraMap ℚ GoodRing) (2 : ℚ)⁻¹ *
        (2 : GoodRing) = 1 := by
  rw [← map_ofNat (algebraMap ℚ GoodRing) 2,
    ← map_mul]
  norm_num

private theorem two_mul_invTwo_sextic :
    (2 : SexticRing) *
        (algebraMap ℚ SexticRing) (2 : ℚ)⁻¹ = 1 := by
  rw [← map_ofNat (algebraMap ℚ SexticRing) 2,
    ← map_mul]
  norm_num

private theorem toGood_comp_toSextic :
    toGood.comp toSextic = RingHom.id GoodRing := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext_iff.mpr
    intro p
    change
      toGood (toSextic (goodXHom p)) = goodXHom p
    rw [goodXHom_apply, toSextic_xClass, toGood_xClass]
  · change
      toGood (toSextic
        N13GeneralizedMumfordIntegral.yClass) =
          N13GeneralizedMumfordIntegral.yClass
    rw [toSextic_yClass]
    simp [goodYInSextic, sexticYInGood, Algebra.smul_def]
    rw [← mul_assoc, invTwo_mul_two_good, one_mul]

private theorem toSextic_comp_toGood :
    toSextic.comp toGood = RingHom.id SexticRing := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext_iff.mpr
    intro p
    change
      toSextic (toGood (sexticXHom p)) = sexticXHom p
    rw [sexticXHom_apply, toGood_xClass, toSextic_xClass]
  · change
      toSextic (toGood (SexticMumford.yClass M)) =
        SexticMumford.yClass M
    rw [toGood_yClass]
    simp [goodYInSextic, sexticYInGood, Algebra.smul_def]
    rw [map_ofNat, ← mul_assoc, two_mul_invTwo_sextic]
    ring

/-- The coordinate-ring isomorphism induced by completion of the square. -/
def coordinateRingEquiv : GoodRing ≃+* SexticRing where
  toFun := toSextic
  invFun := toGood
  left_inv z := by
    have h := DFunLike.congr_fun toGood_comp_toSextic z
    simpa using h
  right_inv z := by
    have h := DFunLike.congr_fun toSextic_comp_toGood z
    simpa using h
  map_mul' := map_mul toSextic
  map_add' := map_add toSextic

@[simp] theorem coordinateRingEquiv_xClass (p : ℚ[X]) :
    coordinateRingEquiv
        (N13GeneralizedMumfordIntegral.xClass p) =
      SexticMumford.xClass M p :=
  toSextic_xClass p

@[simp] theorem coordinateRingEquiv_yClass :
    coordinateRingEquiv
        N13GeneralizedMumfordIntegral.yClass =
      goodYInSextic :=
  toSextic_yClass

end

end MazurProof.N13GoodSexticCoordinateEquiv
