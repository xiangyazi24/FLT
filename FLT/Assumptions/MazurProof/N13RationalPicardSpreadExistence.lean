import FLT.Assumptions.MazurProof.N13RationalCurvePointPicardRealization
import FLT.Assumptions.MazurProof.N13QuadraticPicardRealization
import FLT.Assumptions.MazurProof.N13DegreeOneGraphPoint

/-!
# Global existence of rational N13 spread lines

Every rational oriented Picard class has a unique balanced Mumford normal
form of affine degree at most two.  A quadratic normal form is covered by the
complete quadratic two-chart realization.  A linear normal form determines
an affine rational curve point after temporarily resetting its independent
infinity orientation.  A constant normal form has the unit affine ideal and
uses the doubled positive-infinity line.

In the constant and linear cases the same proper chart line is retained while
the explicit generic infinity integer is reset to the original normal form's
integer.  This is precisely why the two-chart realization stores the oriented
integer separately from its affine ideal.  The resulting special divisor is
literal and unchanged, while the generic class becomes the desired rational
Picard class after base change.
-/

namespace MazurProof.N13RationalPicardSpreadExistence

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The rational N13 Mumford model. -/
abbrev Modelℚ : SexticMumford.Model ℚ :=
  N13Mumford.model ℚ

/-- The two-adic N13 Mumford model. -/
abbrev Model₂ : SexticMumford.Model N13InfinityBaseChange.Q₂ :=
  N13Mumford.model N13InfinityBaseChange.Q₂

/-- The rational oriented Picard group. -/
abbrev G : Type :=
  N13RationalPointEndgame.G

/-!
## Base change and orientation

The affine Mumford ideal depends only on `u` and `v`; the oriented even-degree
Picard class also records an integer at infinity.  We first base-change the
Mumford data, then use `reorientData` to replace only this independent integer
while retaining the proper line and its special fibre verbatim.
-/

/-- Coefficient extension of a rational balanced Mumford representative. -/
def mapMumford (D : N13Mumford.Mumford ℚ) :
    N13Mumford.Mumford N13InfinityBaseChange.Q₂ :=
  D.mapCoeffs
    N13InfinityBaseChange.ratToQ₂
    N13InfinityBaseChange.ratToQ₂_injective
    (N13InfinityBaseChange.map_n13_f
      N13InfinityBaseChange.ratToQ₂)

/-- Retain both proper chart ideals and their literal special divisor while
resetting the explicit generic infinity orientation to a chosen Mumford
representative. -/
def reorientData
    (D : N13Mumford.Mumford N13InfinityBaseChange.Q₂)
    (R : N13TwoChartPicardRealization.Data) :
    N13TwoChartPicardRealization.Data where
  charts := R.charts
  infinityOrder := (D.nInf : ℤ) - 1
  specialDivisor := R.specialDivisor
  special_affine := R.special_affine
  special_infinity := R.special_infinity

/-- Reorientation realizes the target generic class whenever the retained
proper line has the target Mumford affine ideal. -/
theorem reorientData_toGenericPic
    (D : N13Mumford.Mumford N13InfinityBaseChange.Q₂)
    (R : N13TwoChartPicardRealization.Data)
    (hmap :
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          R.charts.affineIdeal =
        SexticMumford.mumfordIdeal Model₂ D.u D.v) :
    (reorientData D R).toGenericPic =
      SexticMumford.classOf
        Model₂
        (N13Infinity.positiveInfinityOrder
          N13InfinityBaseChange.Q₂)
        D := by
  -- The generic-class formula for a two-chart line reads its affine ideal and
  -- the stored infinity order separately.  `reorientData` was chosen so that
  -- these two inputs are exactly those of `D`.
  exact
    N13TwoChartPicardRealization.genericClass_eq_classOf_of_map_affineIdeal_eq
      R.charts D hmap

/-- Reorientation retains the stronger representative-level equality, not
merely equality after passage to the Picard quotient.

This exact raw equality records both the mapped affine fractional ideal and
the oriented integer at infinity.  It is the datum needed later when a
specialization argument must compare the canonical Mumford representative
with the actual integral two-chart line that realizes it. -/
theorem reorientData_genericRaw
    (D : N13Mumford.Mumford N13InfinityBaseChange.Q₂)
    (R : N13TwoChartPicardRealization.Data)
    (hmap :
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          R.charts.affineIdeal =
        SexticMumford.mumfordIdeal Model₂ D.u D.v) :
    N13TwoChartPicardRealization.genericRaw
        (reorientData D R).charts
        (reorientData D R).infinityOrder =
      SexticMumford.mumfordRaw Model₂ D := by
  exact
    N13TwoChartPicardRealization.genericRaw_eq_mumfordRaw_of_map_affineIdeal_eq
      R.charts D hmap

/-!
## Mumford degree zero

A monic constant `u` is `1`, and reducedness then forces `v = 0`.  Thus the
affine ideal is the unit Mumford ideal, already realized by the positive
infinity line.  Only the independent infinity orientation has to be restored.
-/

/-- A degree-zero rational normal form is realized by the doubled positive
infinity line, with its independent generic orientation reset to the normal
form's infinity integer. -/
theorem exists_data_of_natDegree_eq_zero
    (D : N13Mumford.Mumford ℚ)
    (hdeg : D.u.natDegree = 0) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw Model₂ (mapMumford D) ∧
      R.toGenericPic =
          SexticMumford.classOf
            Model₂
            (N13Infinity.positiveInfinityOrder
              N13InfinityBaseChange.Q₂)
            (mapMumford D) := by
  -- Monicity and reducedness collapse the affine Mumford data to `(1, 0)`.
  have hu : D.u = 1 :=
    Polynomial.eq_one_of_monic_natDegree_zero D.u_monic hdeg
  have hv : D.v = 0 := by
    have hreduce := D.v_reduced
    rw [hu] at hreduce
    simpa using hreduce.symm
  let R₀ : N13TwoChartPicardRealization.Data :=
    N13InfinityPointPicardRealization.infinityPlusData
  -- Base change preserves these two polynomials, so the mapped affine ideal
  -- is literally the zero representative's unit ideal.
  have hu₂ :
      (mapMumford D).u =
        (SexticMumford.zero Model₂).u := by
    simp [mapMumford, hu, SexticMumford.zero]
  have hv₂ :
      (mapMumford D).v =
        (SexticMumford.zero Model₂).v := by
    simp [mapMumford, hv, SexticMumford.zero]
  have hmap :
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          R₀.charts.affineIdeal =
        SexticMumford.mumfordIdeal
          Model₂ (mapMumford D).u (mapMumford D).v := by
    change
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          N13InfinityPointPicardRealization.infinityPlusLine.affineIdeal =
        _
    rw [N13InfinityPointPicardRealization.map_infinityPlusLine_affineIdeal]
    rw [hu₂, hv₂]
  -- Reorientation leaves that proper line and its special divisor unchanged
  -- while restoring the original normal form's `nInf`.
  refine ⟨reorientData (mapMumford D) R₀, ?_, ?_⟩
  · exact reorientData_genericRaw (mapMumford D) R₀ hmap
  · exact reorientData_toGenericPic (mapMumford D) R₀ hmap

/-!
## Mumford degree one

After setting `nInf` to zero, a linear Mumford graph is exactly the graph of a
rational affine curve point.  We realize that point by the integral or
escaping two-adic line, prove equality of its affine ideal with the original
graph, and finally restore the graph's original infinity orientation.
-/

/-- Resetting only `nInf` to zero turns a linear balanced graph into the
standard balanced representative of its affine rational curve point. -/
def degreeOnePointForm
    (D : N13Mumford.Mumford ℚ)
    (hdeg : D.u.natDegree = 1) :
    N13Mumford.Mumford ℚ where
  u := D.u
  v := D.v
  nInf := 0
  u_monic := D.u_monic
  deg_u := D.deg_u
  v_reduced := D.v_reduced
  curve_dvd := D.curve_dvd
  infinity_bound := by
    rw [hdeg]
    norm_num

/-- A degree-one rational normal form is realized by the proper line of its
underlying affine point, with the original infinity orientation restored. -/
theorem exists_data_of_natDegree_eq_one
    (D : N13Mumford.Mumford ℚ)
    (hdeg : D.u.natDegree = 1) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw Model₂ (mapMumford D) ∧
      R.toGenericPic =
          SexticMumford.classOf
            Model₂
            (N13Infinity.positiveInfinityOrder
              N13InfinityBaseChange.Q₂)
            (mapMumford D) := by
  -- Removing only the orientation exposes the affine point encoded by the
  -- linear graph; the affine polynomials themselves are not changed.
  let D₀ := degreeOnePointForm D hdeg
  obtain ⟨x, y, hcurve, hpoint⟩ :=
    SexticMumford.exists_affinePoint_of_natDegree_eq_one
      Modelℚ D₀ (by simpa [D₀, degreeOnePointForm] using hdeg) rfl
  let P : N13RationalPointEndgame.RationalCurvePoint :=
    .affine x y hcurve
  -- The point-extraction theorem identifies the reset representative with
  -- `pointMumford P`; project this equality to the two affine polynomials.
  have hu :
      D.u =
        (SexticMumford.pointMumford Modelℚ P).u := by
    simpa [D₀, degreeOnePointForm, P,
      SexticMumford.pointMumford] using
        congrArg SexticMumford.Mumford.u hpoint
  have hv :
      D.v =
        (SexticMumford.pointMumford Modelℚ P).v := by
    simpa [D₀, degreeOnePointForm, P,
      SexticMumford.pointMumford] using
        congrArg SexticMumford.Mumford.v hpoint
  have hu₂ :
      (N13RationalCurvePointPicardRealization.mappedPointMumford P).u =
        (mapMumford D).u := by
    change
      (SexticMumford.pointMumford Modelℚ P).u.map
          N13InfinityBaseChange.ratToQ₂ =
        D.u.map N13InfinityBaseChange.ratToQ₂
    rw [hu]
  have hv₂ :
      (N13RationalCurvePointPicardRealization.mappedPointMumford P).v =
        (mapMumford D).v := by
    change
      (SexticMumford.pointMumford Modelℚ P).v.map
          N13InfinityBaseChange.ratToQ₂ =
        D.v.map N13InfinityBaseChange.ratToQ₂
    rw [hv]
  -- The valuation dichotomy chooses which proper integral closure of the
  -- point exists.  Both branches have the same mapped generic Mumford ideal.
  by_cases hx : ‖N13ProperCurveReduction.ratToQ₂ x‖ ≤ 1
  · let R₀ : N13TwoChartPicardRealization.Data :=
      (N13RationalCurvePointPicardRealization.integralAffineData
        x y hcurve hx).realization
    have hmap :
        Ideal.map
            N13IntegralFractionalHull.integralToRational
            R₀.charts.affineIdeal =
          SexticMumford.mumfordIdeal
            Model₂ (mapMumford D).u (mapMumford D).v := by
      calc
        Ideal.map
              N13IntegralFractionalHull.integralToRational
              R₀.charts.affineIdeal =
            SexticMumford.mumfordIdeal
              Model₂
              (N13RationalCurvePointPicardRealization.mappedPointMumford P).u
              (N13RationalCurvePointPicardRealization.mappedPointMumford P).v :=
          N13RationalCurvePointPicardRealization.integralAffineData_map_affineIdeal
            x y hcurve hx
        _ =
            SexticMumford.mumfordIdeal
              Model₂ (mapMumford D).u (mapMumford D).v := by
          rw [hu₂, hv₂]
    -- The integral point line supplies the affine ideal; reorientation adds
    -- back the original infinity component without changing specialization.
    refine ⟨reorientData (mapMumford D) R₀, ?_, ?_⟩
    · exact reorientData_genericRaw (mapMumford D) R₀ hmap
    · exact reorientData_toGenericPic (mapMumford D) R₀ hmap
  · have hxval :
        (N13ProperCurveReduction.ratToQ₂ x).valuation < 0 :=
      lt_of_not_ge
        ((Padic.norm_le_one_iff_val_nonneg
          (N13ProperCurveReduction.ratToQ₂ x)).not.mp hx)
    -- Outside the norm ball the proper closure uses the escaping chart, but
    -- its generic affine ideal is still the same point graph.
    let R₀ : N13TwoChartPicardRealization.Data :=
      (N13RationalCurvePointPicardRealization.escapingAffineData
        x y hcurve hxval).realization
    have hmap :
        Ideal.map
            N13IntegralFractionalHull.integralToRational
            R₀.charts.affineIdeal =
          SexticMumford.mumfordIdeal
            Model₂ (mapMumford D).u (mapMumford D).v := by
      calc
        Ideal.map
              N13IntegralFractionalHull.integralToRational
              R₀.charts.affineIdeal =
            SexticMumford.mumfordIdeal
              Model₂
              (N13RationalCurvePointPicardRealization.mappedPointMumford P).u
              (N13RationalCurvePointPicardRealization.mappedPointMumford P).v :=
          N13RationalCurvePointPicardRealization.escapingAffineData_map_affineIdeal
            x y hcurve hxval
        _ =
            SexticMumford.mumfordIdeal
              Model₂ (mapMumford D).u (mapMumford D).v := by
          rw [hu₂, hv₂]
    refine ⟨reorientData (mapMumford D) R₀, ?_, ?_⟩
    · exact reorientData_genericRaw (mapMumford D) R₀ hmap
    · exact reorientData_toGenericPic (mapMumford D) R₀ hmap

/-!
## Mumford degree two and the global exhaustion

Quadratic representatives are handled by the previously constructed
two-chart quadratic realization.  Balanced genus-two Mumford forms have
degree at most two, so the constant, linear, and quadratic constructions
exhaust every rational normal form.
-/

/-- A degree-two rational normal form is realized by the complete quadratic
two-chart construction after coefficient extension. -/
theorem exists_data_of_natDegree_eq_two
    (D : N13Mumford.Mumford ℚ)
    (hdeg : D.u.natDegree = 2) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw Model₂ (mapMumford D) ∧
      R.toGenericPic =
          SexticMumford.classOf
            Model₂
            (N13Infinity.positiveInfinityOrder
              N13InfinityBaseChange.Q₂)
            (mapMumford D) := by
  -- Injective coefficient extension preserves the degree of the monic
  -- quadratic polynomial, allowing direct use of the quadratic realization.
  have hdeg₂ : (mapMumford D).u.natDegree = 2 := by
    rw [mapMumford, SexticMumford.mapCoeffs_u,
      Polynomial.natDegree_map_eq_of_injective
        N13InfinityBaseChange.ratToQ₂_injective,
      hdeg]
  obtain ⟨R, hraw, hgeneric⟩ :=
    N13QuadraticPicardRealization.exists_data
      (mapMumford D) hdeg₂
  exact ⟨R, hraw, hgeneric⟩

/-- Every rational balanced Mumford representative has complete two-fibre
Picard data after base change. -/
theorem exists_data (D : N13Mumford.Mumford ℚ) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw Model₂ (mapMumford D) ∧
      R.toGenericPic =
          SexticMumford.classOf
            Model₂
            (N13Infinity.positiveInfinityOrder
              N13InfinityBaseChange.Q₂)
            (mapMumford D) := by
  -- Balancedness gives `deg u ≤ 2`; arithmetic on naturals turns this bound
  -- into the three geometric cases proved above.
  have hbound : D.u.natDegree ≤ 2 := D.deg_u
  have hcases :
      D.u.natDegree = 0 ∨
        D.u.natDegree = 1 ∨
          D.u.natDegree = 2 := by
    omega
  rcases hcases with hzero | hone | htwo
  · exact exists_data_of_natDegree_eq_zero D hzero
  · exact exists_data_of_natDegree_eq_one D hone
  · exact exists_data_of_natDegree_eq_two D htwo

/-!
## From representatives to rational Picard classes

Normalize an arbitrary oriented Picard class, realize that balanced Mumford
representative, and transport the generic equality back through base change.
The resulting spread line deliberately stores the original class rather than
the chosen representative.  We also retain equality of the raw oriented
fractional ideal with the mapped normal form, since later specialization
geometry must compare actual representatives before passing to a quotient.
-/

/-- The unique balanced rational Mumford representative selected for a
Picard class.  Naming it makes the exact generic representative carried by
the chosen spread visible to later files. -/
def normalizedMumford (P : G) : N13Mumford.Mumford ℚ :=
  SexticMumford.normalize
    Modelℚ
    (N13Infinity.positiveInfinityOrder ℚ)
    P

/-- Every rational Picard class has a spread whose generic raw datum is
literally the coefficient extension of its balanced normal form.

The equality is stronger than the previously exposed Picard-class equality:
it fixes both the affine fractional ideal and the infinity orientation.  This
is the canonical representative certificate required by any future
vertical-twist or special-fibre comparison. -/
theorem exists_exactSpreadLine (P : G) :
    ∃ L : N13RationalCurvePointPicardRealization.SpreadLine,
      L.rationalClass = P ∧
      N13TwoChartPicardRealization.genericRaw
          L.realization.charts L.realization.infinityOrder =
        SexticMumford.mumfordRaw Model₂
          (mapMumford (normalizedMumford P)) := by
  obtain ⟨R, hraw, hR⟩ := exists_data (normalizedMumford P)
  -- Naturality of `classOf` identifies the realized two-adic class with the
  -- base change of `P`; normalization is removed in the final equality.
  have hgeneric :
      R.toGenericPic =
        N13InfinityBaseChange.picMapRatToQ₂ P := by
    calc
      R.toGenericPic =
          SexticMumford.classOf
            Model₂
            (N13Infinity.positiveInfinityOrder
              N13InfinityBaseChange.Q₂)
            (mapMumford (normalizedMumford P)) := hR
      _ =
          N13InfinityBaseChange.picMapRatToQ₂
            (SexticMumford.classOf
              Modelℚ
              (N13Infinity.positiveInfinityOrder ℚ)
              (normalizedMumford P)) := by
        exact
          (N13InfinityBaseChange.picMapRatToQ₂_classOf
            (normalizedMumford P)).symm
      _ = N13InfinityBaseChange.picMapRatToQ₂ P := by
        rw [show
          SexticMumford.classOf
              Modelℚ
              (N13Infinity.positiveInfinityOrder ℚ)
              (normalizedMumford P) = P by
            simp [normalizedMumford]]
  exact
    ⟨{ rationalClass := P
       realization := R
       generic_eq := hgeneric }, rfl, hraw⟩

/-- Fix one exact normalized spread for each rational Picard class.  The
choice is made only after the representative-level existence theorem; its
two projection lemmas below prevent later arguments from depending on how
the witness was selected. -/
def exactSpreadLine (P : G) :
    N13RationalCurvePointPicardRealization.SpreadLine :=
  Classical.choose (exists_exactSpreadLine P)

/-- The selected exact spread still stores the rational class from which its
balanced normal form was constructed. -/
@[simp] theorem exactSpreadLine_rationalClass (P : G) :
    (exactSpreadLine P).rationalClass = P :=
  (Classical.choose_spec (exists_exactSpreadLine P)).1

/-- The selected spread carries exactly the mapped balanced Mumford datum,
including its infinity orientation. -/
theorem exactSpreadLine_genericRaw (P : G) :
    N13TwoChartPicardRealization.genericRaw
        (exactSpreadLine P).realization.charts
        (exactSpreadLine P).realization.infinityOrder =
      SexticMumford.mumfordRaw Model₂
        (mapMumford (normalizedMumford P)) :=
  (Classical.choose_spec (exists_exactSpreadLine P)).2

/-- The affine lattice of the selected exact spread extends to the literal
Mumford graph ideal of the mapped rational normal form.

This is the ideal-valued projection of `exactSpreadLine_genericRaw`; it is
recorded separately because canonical contraction compares integral ideals,
whereas the oriented raw datum also carries an independent infinity order. -/
theorem exactSpreadLine_map_affineIdeal (P : G) :
    Ideal.map
        N13IntegralFractionalHull.integralToRational
        (exactSpreadLine P).realization.charts.affineIdeal =
      SexticMumford.mumfordIdeal Model₂
        (mapMumford (normalizedMumford P)).u
        (mapMumford (normalizedMumford P)).v := by
  exact
    N13TwoChartPicardRealization.map_affineIdeal_eq_of_genericRaw_eq_mumfordRaw
      (exactSpreadLine P).realization.charts
      (exactSpreadLine P).realization.infinityOrder
      (mapMumford (normalizedMumford P))
      (exactSpreadLine_genericRaw P)

/-- Every rational oriented Picard class has a concrete rational spread line
whose stored rational class is literally the original class. -/
theorem exists_spreadLine (P : G) :
    ∃ L : N13RationalCurvePointPicardRealization.SpreadLine,
      L.rationalClass = P :=
  ⟨exactSpreadLine P, exactSpreadLine_rationalClass P⟩

/-- Consequently the global spread-existence field of the relation-first
classifier is proved for every proposed reduction kernel. -/
theorem exists_spread
    (kernel : AddSubgroup G)
    (P : G) :
    ∃ L : N13RationalCurvePointPicardRealization.SpreadLine,
      N13RationalCurvePointPicardRealization.genericClass kernel L =
        QuotientAddGroup.mk' kernel P := by
  -- Because the spread line stores `P` literally, its image in any proposed
  -- kernel quotient is definitionally the required generic class.
  obtain ⟨L, rfl⟩ := exists_spreadLine P
  exact ⟨L, rfl⟩

end

end MazurProof.N13RationalPicardSpreadExistence
