import FLT.Assumptions.MazurProof.N13TwoAdicMumfordTransport

/-!
# Base change of the N13 integral coordinate ring to `ℚ₂`

Coefficient extension from `ℤ₂` to `ℚ₂` induces a map between the two
generalized-hyperelliptic coordinate rings.  It carries an integral Mumford
graph ideal exactly onto the graph ideal obtained by coefficient extension.
Composing with completion of the square therefore sends the integral graph
directly to the standard sextic Mumford graph over `ℚ₂`.
-/

open Polynomial

namespace MazurProof.N13TwoAdicCoordinateBaseChange

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13TwoAdicMumfordTransport.R₂

abbrev Q₂ : Type :=
  N13TwoAdicMumfordTransport.Q₂

abbrev IntegralRing : Type :=
  N13GeneralizedMumfordIntegral.CoordinateRing (R := R₂)

abbrev GoodRing : Type :=
  N13GeneralizedMumfordIntegral.CoordinateRing (R := Q₂)

def coeffMap : R₂ →+* Q₂ :=
  N13TwoAdicMumfordTransport.coeffMap

def mapPoly : R₂[X] →+* Q₂[X] :=
  N13TwoAdicMumfordTransport.mapPoly

@[simp] theorem mapPoly_apply (p : R₂[X]) :
    mapPoly p = p.map coeffMap := rfl

@[simp] theorem mapPoly_hPoly :
    mapPoly
        (N13GeneralizedMumfordIntegral.hPoly (R := R₂)) =
      N13GeneralizedMumfordIntegral.hPoly (R := Q₂) :=
  N13TwoAdicMumfordTransport.mapPoly_hPoly

@[simp] theorem mapPoly_rhsPoly :
    mapPoly
        (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)) =
      N13GeneralizedMumfordIntegral.rhsPoly (R := Q₂) :=
  N13TwoAdicMumfordTransport.mapPoly_rhsPoly

theorem map_curvePoly :
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)).map
        mapPoly =
      N13GeneralizedMumfordIntegral.curvePoly (R := Q₂) := by
  simp only [N13GeneralizedMumfordIntegral.curvePoly,
    Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_mul]
  change
    X ^ 2 +
          C (mapPoly
            (N13GeneralizedMumfordIntegral.hPoly (R := R₂))) * X -
        C (mapPoly
          (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂))) =
      X ^ 2 +
          C (N13GeneralizedMumfordIntegral.hPoly (R := Q₂)) * X -
        C (N13GeneralizedMumfordIntegral.rhsPoly (R := Q₂))
  rw [mapPoly_hPoly, mapPoly_rhsPoly]

private theorem target_curve_dvd :
    N13GeneralizedMumfordIntegral.curvePoly (R := Q₂) ∣
      (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)).map
        mapPoly := by
  rw [map_curvePoly]

/-- Coefficient extension on the affine coordinate ring of the good model. -/
def extendCoordinate : IntegralRing →+* GoodRing :=
  AdjoinRoot.map mapPoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    (N13GeneralizedMumfordIntegral.curvePoly (R := Q₂))
    target_curve_dvd

@[simp] theorem extend_xClass (p : R₂[X]) :
    extendCoordinate
        (N13GeneralizedMumfordIntegral.xClass (R := R₂) p) =
      N13GeneralizedMumfordIntegral.xClass
        (R := Q₂) (mapPoly p) := by
  exact AdjoinRoot.map_of
    mapPoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    (N13GeneralizedMumfordIntegral.curvePoly (R := Q₂))
    target_curve_dvd p

@[simp] theorem extend_yClass :
    extendCoordinate
        (N13GeneralizedMumfordIntegral.yClass (R := R₂)) =
      N13GeneralizedMumfordIntegral.yClass (R := Q₂) := by
  exact AdjoinRoot.map_root
    mapPoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    (N13GeneralizedMumfordIntegral.curvePoly (R := Q₂))
    target_curve_dvd

@[simp] theorem extend_ySubClass (v : R₂[X]) :
    extendCoordinate
        (N13GeneralizedMumfordIntegral.ySubClass (R := R₂) v) =
      N13GeneralizedMumfordIntegral.ySubClass
        (R := Q₂) (mapPoly v) := by
  simp [N13GeneralizedMumfordIntegral.ySubClass]

/-- Coefficient extension maps an integral graph ideal onto the
coefficient-extended graph ideal. -/
theorem map_mumfordIdeal (u v : R₂[X]) :
    Ideal.map extendCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) u v) =
      N13GeneralizedMumfordIntegral.mumfordIdeal
        (R := Q₂) (mapPoly u) (mapPoly v) := by
  rw [N13GeneralizedMumfordIntegral.mumfordIdeal,
    N13GeneralizedMumfordIntegral.mumfordIdeal,
    Ideal.map_span, Set.image_pair, extend_xClass,
    extend_ySubClass]

/-- The full integral-to-sextic coordinate map over `ℚ₂`. -/
def integralToSextic :
    IntegralRing →+*
      N13GoodSexticCoordinateEquiv.SexticRing (K := Q₂) :=
  (N13GoodSexticCoordinateEquiv.toSextic (K := Q₂)).comp
    extendCoordinate

/-- An integral smooth graph ideal becomes exactly the standard reduced
sextic Mumford graph attached by `sexticSemi`. -/
theorem map_mumfordIdeal_sexticSemi
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    Ideal.map integralToSextic
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) D.u D.v) =
      SexticMumford.mumfordIdeal
        (N13GoodSexticCoordinateEquiv.M (K := Q₂))
        (N13TwoAdicMumfordTransport.sexticSemi D nInf).u
        (N13TwoAdicMumfordTransport.sexticSemi D nInf).v := by
  rw [integralToSextic, ← Ideal.map_map,
    map_mumfordIdeal]
  exact
    N13TwoAdicMumfordTransport.map_mumfordIdeal_sexticSemi
      D nInf

end

end MazurProof.N13TwoAdicCoordinateBaseChange
