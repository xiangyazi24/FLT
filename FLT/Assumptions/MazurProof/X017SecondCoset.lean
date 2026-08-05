import FLT.Assumptions.MazurProof.X017FirstCoset

/-!
# The source quotient in the `X₀(17)` two-isogeny descent

The remaining isogeny quotient is the source modulo the image of the dual
map.  Its nontrivial first-coordinate squareclass is represented by the
order-four point `T=(17,136)`.  Translation by `-T` converts that class into
a square, after which the explicit dual-isogeny preimage formula applies.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.X017SecondCoset

open WeierstrassCurve
open WeierstrassCurve.Affine
open MazurProof.StandardTwoIsogenyPreimages
open MazurProof.VeluTwoIsogeny
open MazurProof.X017Descent
open MazurProof.X017FirstCoset
open MazurProof.X017IsogenySequence
open MazurProof.X017Model

noncomputable section

/-! ## Translation of the `17`-squareclass by `T` -/

/-- For a nonzero affine source point with `x=17r²` and `x≠17`, the first
coordinate after translating by `-T` is an explicit rational square. -/
theorem sub_T_addX_square
    {x y r : ℚ} (h : Nonsingular standard x y)
    (hx0 : x ≠ 0) (hx17 : x ≠ 17) (hr : x = 17 * r ^ 2) :
    addX standard x 17
        (slope standard x 17 y (-136)) =
      ((y + 8 * x) / (r * (x - 17))) ^ 2 := by
  have hr0 : r ≠ 0 := by
    intro hrz
    apply hx0
    rw [hr, hrz]
    norm_num
  have hcurve :=
    (StandardTwoIsogeny.curve_equation
      (a := a17) (b := b17)).mp h.left
  norm_num [a17, b17, veluT] at hcurve
  have hrsq1 : r ^ 2 ≠ 1 := by
    intro hrsq
    apply hx17
    rw [hr, hrsq]
    norm_num
  rw [slope_of_X_ne hx17]
  norm_num [standard, StandardTwoIsogeny.curve, addX]
  rw [hr] at hcurve ⊢
  field_simp [hr0, hrsq1]
  nlinarith [hcurve]

/-! ## Explicit dual preimages -/

/-- A nonzero square first coordinate on the standard source has a preimage
under the bundled dual isogeny. -/
theorem exists_dualHom_preimage_of_x_eq_sq
    {x y r : ℚ} (h : Nonsingular standard x y)
    (hx : x ≠ 0) (hr : x = r ^ 2) :
    ∃ Q : Point standardDual,
      dualHom Q = Point.some x y h := by
  obtain ⟨Q, hQ⟩ :=
    exists_dualPoint_preimage_of_x_eq_sq
      (a := a17) (b := b17) h hx hr
  exact ⟨Q, by rw [dualHom_apply, hQ]⟩

/-! ## Exceptional visible points -/

/-- The negative of `T` has the expected affine coordinates. -/
private theorem neg_T_eq_some :
    -T =
      Point.some 17 (-136)
        (equation_iff_nonsingular.mp
          (StandardTwoIsogeny.curve_equation.mpr (by
            norm_num [a17, b17, veluT]))) := by
  unfold T
  rw [Point.neg_some, Point.some.injEq]
  constructor
  · rfl
  · norm_num [StandardTwoIsogeny.curve_negY]

/-- The other point over the first coordinate `17` differs from `T` by the
source kernel point. -/
private theorem neg_T_eq_T_add_K : -T = T + K := by
  apply add_left_cancel (a := T)
  rw [add_neg_cancel, ← add_assoc, ← two_nsmul, two_nsmul_T_eq_K]
  exact (StandardTwoIsogeny.kernel_add_self
    (a := a17) (b := b17)).symm

/-- The two affine source points above `x=17` are `T` and `-T`. -/
private theorem source_x_seventeen
    {y : ℚ} (h : Nonsingular standard 17 y) :
    (Point.some 17 y h : Point standard) = T ∨
      (Point.some 17 y h : Point standard) = -T := by
  have hcurve :=
    (StandardTwoIsogeny.curve_equation
      (a := a17) (b := b17)).mp h.left
  norm_num [a17, b17, veluT] at hcurve
  have hfactor : (y - 136) * (y + 136) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hy | hy
  · left
    unfold T
    rw [Point.some.injEq]
    exact ⟨rfl, by linarith⟩
  · right
    rw [neg_T_eq_some, Point.some.injEq]
    exact ⟨rfl, by linarith⟩

/-! ## The second concrete isogeny quotient -/

/-- The source of the standard N17 two-isogeny is covered by the dual image
and its translate by the visible order-four point `T`. -/
theorem source_twoCosetExhaustion :
    MazurProof.X017ExactSequence.TwoCosetExhaustion dualHom T := by
  intro P
  cases P with
  | zero =>
      exact ⟨0, Or.inl (map_zero dualHom).symm⟩
  | some x y h =>
      by_cases hx0 : x = 0
      · have hy : y = 0 :=
          StandardTwoIsogeny.y_zero_of_x_zero h hx0
        have hPK :
            (Point.some x y h : Point standard) = K := by
          unfold K StandardTwoIsogeny.kernelPoint
          rw [Point.some.injEq]
          exact ⟨hx0, hy⟩
        exact ⟨U, Or.inl (by rw [hPK, dualHom_U])⟩
      · obtain ⟨q, hq | hq⟩ :=
          source_x_squareclass h.left hx0
        · obtain ⟨Q, hQ⟩ :=
            exists_dualHom_preimage_of_x_eq_sq h hx0 hq
          exact ⟨Q, Or.inl hQ.symm⟩
        · by_cases hx17 : x = 17
          · have h17 : Nonsingular standard 17 y := hx17 ▸ h
            have hP17 :
                (Point.some x y h : Point standard) =
                  Point.some 17 y h17 := by
              rw [Point.some.injEq]
              exact ⟨hx17, rfl⟩
            rcases source_x_seventeen h17 with hT | hnegT
            · exact
                ⟨0, Or.inr (by
                  rw [hP17, hT, map_zero, add_zero])⟩
            · refine ⟨U, Or.inr ?_⟩
              rw [hP17, hnegT, dualHom_U, neg_T_eq_T_add_K]
          · have hq0 : q ≠ 0 := by
              intro hqz
              apply hx0
              rw [hq, hqz]
              norm_num
            have hnum0 : y + 8 * x ≠ 0 := by
              intro hnum
              have hy : y = -8 * x := by linarith
              have hcurve :=
                (StandardTwoIsogeny.curve_equation
                  (a := a17) (b := b17)).mp h.left
              norm_num [a17, b17, veluT] at hcurve
              rw [hy] at hcurve
              have hfactor : x * (x - 17) ^ 2 = 0 := by
                nlinarith
              have hsquare : (x - 17) ^ 2 = 0 :=
                (mul_eq_zero.mp hfactor).resolve_left hx0
              exact hx17 (sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare))
            generalize hR :
                (Point.some x y h : Point standard) - T = R
            cases R with
            | zero =>
                have hR' := hR
                rw [sub_eq_add_neg, neg_T_eq_some,
                  Point.add_of_X_ne hx17] at hR'
                exact ((Point.some_ne_zero _) hR').elim
            | some x' y' h' =>
                have hx' :
                    x' =
                      addX standard x 17
                        (slope standard x 17 y (-136)) := by
                  have hR' := hR
                  rw [sub_eq_add_neg, neg_T_eq_some,
                    Point.add_of_X_ne hx17] at hR'
                  rw [Point.some.injEq] at hR'
                  exact hR'.1.symm
                let q' : ℚ :=
                  (y + 8 * x) / (q * (x - 17))
                have hxSquare : x' = q' ^ 2 := by
                  rw [hx', sub_T_addX_square h hx0 hx17 hq]
                have hq'0 : q' ≠ 0 := by
                  exact div_ne_zero hnum0
                    (mul_ne_zero hq0 (sub_ne_zero.mpr hx17))
                have hx'0 : x' ≠ 0 := by
                  rw [hxSquare]
                  exact pow_ne_zero 2 hq'0
                obtain ⟨Q, hQ⟩ :=
                  exists_dualHom_preimage_of_x_eq_sq h' hx'0 hxSquare
                have hrange :
                    (Point.some x y h : Point standard) - T =
                      dualHom Q :=
                  hR.trans hQ.symm
                refine ⟨Q, Or.inr ?_⟩
                calc
                  (Point.some x y h : Point standard) =
                      T + (Point.some x y h - T) := by
                    abel
                  _ = T + dualHom Q := by
                    rw [hrange]

/-! ## Cardinality of the right endpoint and the doubling quotient -/

/-- The two displayed source representatives map from `Bool` onto the right
isogeny quotient. -/
noncomputable def rightQuotientRep :
    Bool → Point standard ⧸ dualHom.range
  | false => 0
  | true => (T : Point standard ⧸ dualHom.range)

/-- The source coset exhaustion makes the two-element representative map
surjective. -/
theorem rightQuotientRep_surjective :
    Function.Surjective rightQuotientRep := by
  intro q
  induction q using QuotientAddGroup.induction_on with
  | _ P =>
      obtain ⟨Q, hP | hP⟩ := source_twoCosetExhaustion P
      · refine ⟨false, ?_⟩
        change (0 : Point standard ⧸ dualHom.range) = (P : _)
        symm
        exact
          (QuotientAddGroup.eq_zero_iff P).mpr
            ⟨Q, hP.symm⟩
      · refine ⟨true, ?_⟩
        change (T : Point standard ⧸ dualHom.range) = (P : _)
        symm
        rw [QuotientAddGroup.eq_iff_sub_mem]
        refine ⟨Q, ?_⟩
        rw [hP]
        abel

/-- The right isogeny quotient inherits a finite structure from its two
explicit representatives. -/
@[implicit_reducible] noncomputable def rightQuotientFintype :
    Fintype (Point standard ⧸ dualHom.range) := by
  classical
  exact Fintype.ofSurjective rightQuotientRep
    rightQuotientRep_surjective

/-- The independent right endpoint of the N17 two-isogeny descent has at
most two elements. -/
theorem natCard_rightQuotient_le_two :
    Nat.card (Point standard ⧸ dualHom.range) ≤ 2 := by
  letI : Fintype (Point standard ⧸ dualHom.range) :=
    rightQuotientFintype
  have hcard :=
    Nat.card_le_card_of_surjective rightQuotientRep
      rightQuotientRep_surjective
  simpa using hcard

/-- The completed first coset calculation and finite right endpoint give a
finite structure on the source modulo doubling. -/
@[implicit_reducible] noncomputable def doubleQuotientFintype :
    Fintype
      (MazurProof.RationalPointsN15ExactSequence.DoubleQuotient
        (Point standard)) := by
  letI : Fintype (Point standard ⧸ dualHom.range) :=
    rightQuotientFintype
  exact
    MazurProof.X017ExactSequence.middleFintype_of_leftMap_eq_zero
      forwardHom dualHom dual_comp_forward standard_leftMap_eq_zero

/-- The rational standard source has at most two classes modulo doubling. -/
theorem natCard_doubleQuotient_le_two :
    Nat.card
      (MazurProof.RationalPointsN15ExactSequence.DoubleQuotient
        (Point standard)) ≤ 2 := by
  letI : Fintype (Point standard ⧸ dualHom.range) :=
    rightQuotientFintype
  exact
    (MazurProof.X017ExactSequence.natCard_doubleQuotient_le_right
      forwardHom dualHom dual_comp_forward
        standard_leftMap_eq_zero).trans
      natCard_rightQuotient_le_two

/-! ## Representatives modulo doubling -/

/-- Combining the two independent isogeny covers shows directly that every
source point is a double or `T` plus a double. -/
theorem double_twoCosetExhaustion :
    MazurProof.X017ExactSequence.TwoCosetExhaustion
      (nsmulAddMonoidHom (α := Point standard) 2) T := by
  intro P
  obtain ⟨Q, hP | hP⟩ := source_twoCosetExhaustion P
  · obtain ⟨R, hQ | hQ⟩ :=
      standardDual_twoCosetExhaustion Q
    · refine ⟨R, Or.inl ?_⟩
      rw [hP, hQ, dual_comp_forward]
      rfl
    · refine ⟨R, Or.inl ?_⟩
      rw [hP, hQ, map_add, dualHom_eta, zero_add,
        dual_comp_forward]
      rfl
  · obtain ⟨R, hQ | hQ⟩ :=
      standardDual_twoCosetExhaustion Q
    · refine ⟨R, Or.inr ?_⟩
      rw [hP, hQ, dual_comp_forward]
      rfl
    · refine ⟨R, Or.inr ?_⟩
      rw [hP, hQ, map_add, dualHom_eta, zero_add,
        dual_comp_forward]
      rfl

end

end MazurProof.X017SecondCoset
