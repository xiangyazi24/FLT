import FLT.Assumptions.MazurProof.N18RouteC_LocalCubeComparison

/-!
# Actual dual Kummer values survive only on the torsion line

This combines homogeneous integral coordinates, weight-primitivity, the
`pi^5` local table, and the global `S`-unit normal form.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.N18RouteC.DualSurvivor

open FieldArithmetic Isogeny KummerGeometry GlobalCubes LocalThree
open LocalThreeSound DualGlobal DualLocal LocalCubeComparison

noncomputable section

abbrev OL := NumberField.RingOfIntegers L

private theorem pi_ne_zero : pi ≠ 0 := by
  intro hz
  have h := pi_relation
  rw [hz] at h
  norm_num at h

/-- Away from the two kernel points, the Kummer value has a primitive local
presentation with a `pi^(3m)`-normalized numerator accepted by the table. -/
theorem generic_local_normal_form
    {x y : L} (h : WeierstrassCurve.Affine.Nonsingular E0 x y)
    (hx : x ≠ 1) :
    ∃ m : ℕ, ∃ D W₀ : OL,
      D ≠ 0 ∧ W₀ ≠ 0 ∧ ¬piInteger ∣ W₀ ∧
      kappa (.some x y h) =
        pi ^ (3 * m) * (W₀ : L) / (D : L) ^ 3 ∧
      InDualLine (reduceOL W₀) := by
  have hu : tateU x ≠ 0 := sub_ne_zero.mpr hx
  have hnotT : ¬(x = 1 ∧ y = 0) := fun hxy => hx hxy.1
  have hw : tateW x y ≠ 0 := by
    simpa [kappa_some_of_ne_T h hnotT] using kappa_ne_zero (.some x y h)
  have hcurve := translated_curve_equation h
  obtain ⟨U, D, W, hU, hD, hW, hUL, hWL, hhom⟩ :=
    exists_homogeneous_coords hu hw hcurve
  obtain ⟨U', D', W', hU', hD', hW', hhom', hprimitive,
      r, hUfac, hDfac, hWfac⟩ :=
    exists_weight_primitive hU hD hW hhom
  have hWD : (W' : L) = (D' : L) ^ 3 * tateW x y := by
    have hEq := hWL
    rw [hWfac, hDfac] at hEq
    push_cast at hEq
    have hpow : (pi : L) ^ (3 * r) = (pi ^ r) ^ 3 := by
      rw [← pow_mul]
      congr 1
      omega
    simp only [piInteger_coe_L] at hEq
    rw [hpow] at hEq
    have hscaled :
        (pi ^ r) ^ 3 * (W' : L) =
          (pi ^ r) ^ 3 * ((D' : L) ^ 3 * tateW x y) := by
      calc
        _ = (pi ^ r * (D' : L)) ^ 3 * tateW x y := hEq
        _ = _ := by ring
    exact mul_left_cancel₀
      (pow_ne_zero 3 (pow_ne_zero r pi_ne_zero)) hscaled
  obtain ⟨m, W₀, hW₀, hpW₀, hWfac', hline⟩ :=
    primitive_local_value_in_dual_line hU' hD' hW' hhom' hprimitive
  refine ⟨m, D', W₀, hD', hW₀, hpW₀, ?_, hline⟩
  rw [kappa_some_of_ne_T h hnotT]
  have hD'L : (D' : L) ≠ 0 := by exact_mod_cast hD'
  have hfacL := congrArg (fun z : OL ↦ (z : L)) hWfac'
  change (W' : L) = pi ^ (3 * m) * (W₀ : L) at hfacL
  apply (eq_div_iff (pow_ne_zero 3 hD'L)).2
  calc
    tateW x y * (D' : L) ^ 3 = (W' : L) := by rw [hWD]; ring
    _ = pi ^ (3 * m) * (W₀ : L) := hfacL

private theorem affine_x_one_y_cases
    {x y : L} (h : WeierstrassCurve.Affine.Nonsingular E0 x y)
    (hx : x = 1) : y = 0 ∨ y = -2 := by
  have heq := h.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [E0] at heq
  rw [hx] at heq
  have hprod : y * (y + 2) = 0 := by linear_combination heq
  rcases mul_eq_zero.mp hprod with hy | hy
  · exact Or.inl hy
  · exact Or.inr (by linear_combination hy)

/-- Every actual point supplies one of the 81 global records and that record
passes the sound `p3` local predicate. -/
theorem candidate_of_point (P : E0Point) :
    ∃ i j k l : Fin 3, ∃ c : L,
      c ≠ 0 ∧
      kappa P = candidateField i j k * pi ^ l.val * c ^ 3 ∧
      PassDual3Finite i j k l := by
  cases P with
  | zero =>
      refine ⟨0, 0, 0, 0, 1, one_ne_zero, ?_, ?_⟩
      · norm_num [candidateField, kappa]
      · exact (passDual3Finite_iff 0 0 0 0).2 ⟨rfl, rfl, rfl⟩
  | some x y h =>
      by_cases hx : x = 1
      · rcases affine_x_one_y_cases h hx with hy | hy
        · have hP :
              (WeierstrassCurve.Affine.Point.some x y h : E0Point) = T := by
            rw [T, WeierstrassCurve.Affine.Point.some.injEq]
            exact ⟨hx, hy⟩
          rw [hP]
          refine ⟨0, 0, 2, 0, 1 / 2, by norm_num, ?_, ?_⟩
          · norm_num [candidateField, kappa_T]
          · exact (passDual3Finite_iff 0 0 2 0).2 ⟨rfl, rfl, rfl⟩
        · have hP :
              (WeierstrassCurve.Affine.Point.some x y h : E0Point) = negT := by
            rw [negT, WeierstrassCurve.Affine.Point.some.injEq]
            exact ⟨hx, hy⟩
          rw [hP]
          refine ⟨0, 0, 1, 0, -1, by norm_num, ?_, ?_⟩
          · norm_num [candidateField, kappa_negT]
          · exact (passDual3Finite_iff 0 0 1 0).2 ⟨rfl, rfl, rfl⟩
      · obtain ⟨i, j, k, l, c, hglobal⟩ :=
          DualGlobal.kappa_global_normal_form
            (WeierstrassCurve.Affine.Point.some x y h)
        have hglobal' :
            kappa (.some x y h) = candidateField i j k * pi ^ l.val * c ^ 3 := by
          simpa [candidateField, mul_assoc] using hglobal
        have hc : c ≠ 0 := by
          intro hc0
          apply kappa_ne_zero (.some x y h)
          rw [hglobal', hc0]
          norm_num
        obtain ⟨m, D, W₀, hD, hW₀, hpW₀, hlocal, hline⟩ :=
          generic_local_normal_form h hx
        have hpass := global_candidate_passes_p3 i j k l
          (kappa_ne_zero (.some x y h)) hc hD hW₀ hpW₀
          hlocal hglobal' hline
        exact ⟨i, j, k, l, c, hc, hglobal', hpass⟩

/-- The three surviving global classes are represented by `O`, `T`, and
`-T`, with an explicit cube multiplier. -/
theorem kappa_torsion_representative (P : E0Point) :
    ∃ n : Fin 3, ∃ c : L, c ≠ 0 ∧
      kappa P = kappa (n.val • T) * c ^ 3 := by
  obtain ⟨i, j, k, l, c, hc, hglobal, hpass⟩ := candidate_of_point P
  have hcoords := (passDual3Finite_iff i j k l).mp hpass
  rcases hcoords with ⟨rfl, rfl, rfl⟩
  fin_cases k
  · refine ⟨0, c, hc, ?_⟩
    simpa [candidateField] using hglobal
  · refine ⟨2, -c, neg_ne_zero.mpr hc, ?_⟩
    change kappa P = kappa ((2 : ℕ) • T) * (-c) ^ 3
    rw [show (2 : ℕ) • T = negT from two_nsmul_T, kappa_negT]
    have hg : kappa P = 2 * c ^ 3 := by
      simpa [candidateField] using hglobal
    rw [hg]
    ring
  · refine ⟨1, 2 * c, mul_ne_zero (by norm_num) hc, ?_⟩
    change kappa P = kappa ((1 : ℕ) • T) * (2 * c) ^ 3
    rw [one_nsmul, kappa_T]
    have hg : kappa P = (2 : L) ^ 2 * c ^ 3 := by
      simpa [candidateField] using hglobal
    rw [hg]
    ring

/-- Subtracting the matching torsion representative makes the dual Kummer
value an actual cube in `L`. -/
theorem kappa_cube_after_sub_torsion (P : E0Point) :
    ∃ n : Fin 3, ∃ c : L,
      c ^ 3 = kappa (P - n.val • T) := by
  obtain ⟨n, c, hc, hrep⟩ := kappa_torsion_representative P
  fin_cases n
  · refine ⟨0, c, ?_⟩
    change c ^ 3 = kappa (P - (0 : Fin 3).val • T)
    have hrep0 : kappa P = c ^ 3 := by
      change kappa P = kappa ((0 : ℕ) • T) * c ^ 3 at hrep
      simpa using hrep
    calc
      c ^ 3 = kappa P := hrep0.symm
      _ = kappa (P - (0 : Fin 3).val • T) := by
        congr 1
        abel
  · obtain ⟨e, he, hsub⟩ := kappa_sub_T_cube_relation P
    refine ⟨1, -(c * e), ?_⟩
    change (-(c * e)) ^ 3 = kappa (P - T)
    change kappa P = kappa T * c ^ 3 at hrep
    rw [hrep, kappa_T, kappa_negT] at hsub
    rw [hsub]
    ring
  · obtain ⟨e, he, hadd⟩ := kappa_add_T_cube_relation P
    refine ⟨2, -(c * e), ?_⟩
    change (-(c * e)) ^ 3 = kappa (P - (2 : ℕ) • T)
    change kappa P = kappa ((2 : ℕ) • T) * c ^ 3 at hrep
    have hpoint : P - (2 : ℕ) • T = P + T := by
      rw [two_nsmul_T, ← neg_T]
      abel
    rw [hpoint]
    rw [hrep, two_nsmul_T, kappa_negT, kappa_T] at hadd
    rw [hadd]
    ring

end

end MazurProof.N18RouteC.DualSurvivor
