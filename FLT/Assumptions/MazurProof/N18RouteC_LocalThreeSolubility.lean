import FLT.Assumptions.MazurProof.N18RouteC_LocalThreeSolubilityTable

/-!
# Soluble homogeneous Kummer values modulo `pi^5`

This file is kept separate from the quotient-ring implementation so the two
curve-solubility certificates do not force recompilation of the basic
`243`-element ring tables.
-/

namespace MazurProof.N18RouteC.LocalThree

private theorem unitRep_zero_zero (k : F3) :
    unitRep 0 0 k = pow two5 k.val := by
  native_decide +revert

theorem isUnit5_pow {x : R5}
    (hx : IsUnit5 x) (n : ℕ) : IsUnit5 (x ^ n) := by
  induction n with
  | zero => simpa using one_isUnit5
  | succ n ih => rw [pow_succ]; exact isUnit5_mul ih hx

theorem inDualLine_unscale (W s : R5)
    (hs : IsUnit5 s) (hline : InDualLine (W * s ^ 3)) :
    InDualLine W := by
  obtain ⟨m, r, hr, hrel⟩ := hline
  change W * s ^ 3 = pow two5 m.val * r ^ 3 at hrel
  obtain ⟨q, hsq⟩ := exists_right_inverse5 s hs
  refine ⟨m, r * q, isUnit5_mul hr <|
    isUnit5_of_mul_eq_one s q hsq, ?_⟩
  change W = pow two5 m.val * (r * q) ^ 3
  calc
    W = W * (s * q) ^ 3 := by rw [hsq]; simp
    _ = (W * s ^ 3) * q ^ 3 := by ring
    _ = pow two5 m.val * r ^ 3 * q ^ 3 := by rw [hrel]
    _ = pow two5 m.val * (r * q) ^ 3 := by ring

/-- The finite local solubility test for a primitive homogeneous point with
unit Kummer coordinate. -/
theorem homogeneous_unit_value_in_dual_line
    (U D W : R5)
    (hW : IsUnit5 W) (hUD : IsUnit5 U ∨ IsUnit5 D)
    (hcurve : OnHomogeneous U D W) :
    InDualLine W := by
  by_cases hD : IsUnit5 D
  · obtain ⟨s, hDs⟩ := exists_right_inverse5 D hD
    have hs : IsUnit5 s := isUnit5_of_mul_eq_one D s hDs
    have hscaled :
        OnHomogeneous (U * s ^ 2) (D * s) (W * s ^ 3) := by
      unfold OnHomogeneous at hcurve ⊢
      calc
        (W * s ^ 3) *
              (W * s ^ 3 - 3 * (U * s ^ 2) * (D * s) +
                2 * (D * s) ^ 3) =
            (W * (W - 3 * U * D + 2 * D ^ 3)) * s ^ 6 := by ring
        _ = U ^ 3 * s ^ 6 := by rw [hcurve]
        _ = (U * s ^ 2) ^ 3 := by ring
    have hscaled' : OnHomogeneous (U * s ^ 2) 1 (W * s ^ 3) := by
      rwa [hDs] at hscaled
    apply inDualLine_unscale W s hs
    exact homogeneous_d_one (W * s ^ 3)
      (isUnit5_mul hW (isUnit5_pow hs 3)) ⟨U * s ^ 2, hscaled'⟩
  · have hU : IsUnit5 U := hUD.resolve_right hD
    obtain ⟨i, j, k, r, hr, hWrep⟩ := unit_reps_complete W hW
    have hWrepRing : W = unitRep i j k * r ^ 3 := by
      change W = mul (unitRep i j k) (r ^ 3)
      rw [← pow_eq_ring_pow]
      exact hWrep
    obtain ⟨s, hrs⟩ := exists_right_inverse5 r hr
    have hs : IsUnit5 s := isUnit5_of_mul_eq_one r s hrs
    have hscaled :
        OnHomogeneous (U * s ^ 2) (D * s) (W * s ^ 3) := by
      unfold OnHomogeneous at hcurve ⊢
      calc
        (W * s ^ 3) *
              (W * s ^ 3 - 3 * (U * s ^ 2) * (D * s) +
                2 * (D * s) ^ 3) =
            (W * (W - 3 * U * D + 2 * D ^ 3)) * s ^ 6 := by ring
        _ = U ^ 3 * s ^ 6 := by rw [hcurve]
        _ = (U * s ^ 2) ^ 3 := by ring
    have hWscaled : W * s ^ 3 = unitRep i j k := by
      rw [hWrepRing]
      calc
        unitRep i j k * r ^ 3 * s ^ 3 =
            unitRep i j k * (r * s) ^ 3 := by ring
        _ = unitRep i j k := by rw [hrs]; simp
    rw [hWscaled] at hscaled
    have hDscaled : ¬IsUnit5 (D * s) := by
      intro hunit
      apply hD
      have hprod : IsUnit5 ((D * s) * r) := isUnit5_mul hunit hr
      simpa [mul_assoc, mul_comm s r, hrs] using hprod
    obtain ⟨hi, hj⟩ := homogeneous_nonunit_d_rep_coordinates i j k
      (U * s ^ 2) (D * s) (isUnit5_mul hU (isUnit5_pow hs 2))
      hDscaled hscaled
    subst i
    subst j
    refine ⟨k, ?_⟩
    rw [← unitRep_zero_zero k]
    exact ⟨r, hr, hWrep⟩

/-- The only nontrivial positive-valuation chart needed modulo `pi^5`:
`U = pi*U₁`, `W = pi^3*W₁`. -/
theorem scaled_one_unit_value_in_dual_line
    (U D W : R5)
    (hU : IsUnit5 U) (hD : IsUnit5 D) (hW : IsUnit5 W)
    (hcurve : OnScaledOne U D W) :
    InDualLine W := by
  obtain ⟨s, hDs⟩ := exists_right_inverse5 D hD
  have hs : IsUnit5 s := isUnit5_of_mul_eq_one D s hDs
  have hscaled :
      OnScaledOne (U * s ^ 2) (D * s) (W * s ^ 3) := by
    unfold OnScaledOne at hcurve ⊢
    calc
      (W * s ^ 3) *
            (pi5 ^ 3 * (W * s ^ 3) -
              3 * pi5 * (U * s ^ 2) * (D * s) +
              2 * (D * s) ^ 3) =
          (W * (pi5 ^ 3 * W - 3 * pi5 * U * D + 2 * D ^ 3)) *
            s ^ 6 := by ring
      _ = U ^ 3 * s ^ 6 := by rw [hcurve]
      _ = (U * s ^ 2) ^ 3 := by ring
  have hscaled' : OnScaledOne (U * s ^ 2) 1 (W * s ^ 3) := by
    rwa [hDs] at hscaled
  apply inDualLine_unscale W s hs
  exact scaled_one_d_one (W * s ^ 3)
    (isUnit5_mul hW (isUnit5_pow hs 3))
    ⟨U * s ^ 2, isUnit5_mul hU (isUnit5_pow hs 2), hscaled'⟩

end MazurProof.N18RouteC.LocalThree
