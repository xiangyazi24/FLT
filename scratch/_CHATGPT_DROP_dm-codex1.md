```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein
import Mathlib.Algebra.Group.Int.Units
import Mathlib.RingTheory.PrincipalIdealDomain

namespace MazurProof.RationalPointsN12

theorem positive_unit_eq_one {k : ℤ} (hk : 0 < k) (hu : IsUnit k) :
    k = 1 := by
  rcases Int.isUnit_eq_one_or hu with h | h
  · exact h
  · have hbad : (0 : ℤ) < -1 := by
      simpa [h] using hk
    exact False.elim ((by decide : ¬ (0 : ℤ) < -1) hbad)

private theorem isUnit_of_coprime_scaled {X Y A B k : ℤ}
    (hXY : IsCoprime X Y)
    (hX : X = A * k)
    (hY : Y = B * k) :
    IsUnit k := by
  have hkX : k ∣ X := by
    refine ⟨A, ?_⟩
    rw [hX]
    ring
  have hkY : k ∣ Y := by
    refine ⟨B, ?_⟩
    rw [hY]
    ring
  exact hXY.isUnit_of_dvd' hkX hkY

theorem eisenstein_scale_kill_divided {X Y Z m n C EA' EB' : ℤ}
    (hXY : IsCoprime X Y)
    (hnpos : 0 < n) (hYpos : 0 < Y) (hEBpos : 0 < eisensteinEB m n)
    (hEA : eisensteinEA m n = 3 * EA')
    (hEB : eisensteinEB m n = 3 * EB')
    (hEAEB : IsCoprime EA' EB')
    (hZeq : eisensteinEB m n * Z = (m ^ 2 - m * n + n ^ 2) * C)
    (hXeq : eisensteinEB m n * X = eisensteinEA m n * C)
    (hYeq : eisensteinEB m n * Y = (2 * m * n - n ^ 2) * C)
    (hYC : Y = n * C) :
    C = EB' ∧ 3 * X = eisensteinEA m n ∧
      3 * Y = 2 * m * n - n ^ 2 ∧ 3 * Z = m ^ 2 - m * n + n ^ 2 := by
  have hEB'pos : 0 < EB' := by
    have hpos3 : 0 < (3 : ℤ) * EB' := by
      simpa [hEB] using hEBpos
    exact pos_of_mul_pos_left hpos3 (by decide : (0 : ℤ) ≤ 3)
  have hEB'ne : EB' ≠ 0 := ne_of_gt hEB'pos

  -- Divide the `X` scale equation by the literal factor `3`, not by `EB'` yet.
  have hXeq3 : (3 * EB') * X = (3 * EA') * C := by
    simpa [hEB, hEA] using hXeq
  have hXeq' : EB' * X = EA' * C := by
    apply mul_left_cancel₀ (show (3 : ℤ) ≠ 0 by decide)
    calc
      (3 : ℤ) * (EB' * X) = (3 * EB') * X := by ring
      _ = (3 * EA') * C := hXeq3
      _ = (3 : ℤ) * (EA' * C) := by ring

  -- Euclid: `EB' ∣ EA' * C`, and `EA'` is coprime to `EB'`, so `EB' ∣ C`.
  have hEB'_dvd_EA'C : EB' ∣ EA' * C := by
    refine ⟨X, ?_⟩
    exact hXeq'.symm
  have hEB'_dvd_C : EB' ∣ C :=
    hEAEB.symm.dvd_of_dvd_mul_left hEB'_dvd_EA'C
  rcases hEB'_dvd_C with ⟨k, hkC⟩

  -- Positivity of the scale `k`, derived from `Y=n*C` and `EB'>0`.
  have hCpos : 0 < C := by
    have hprod : 0 < n * C := by
      simpa [hYC] using hYpos
    exact pos_of_mul_pos_left hprod (le_of_lt hnpos)
  have hkpos : 0 < k := by
    have hprod : 0 < EB' * k := by
      simpa [hkC] using hCpos
    exact pos_of_mul_pos_left hprod (le_of_lt hEB'pos)

  -- Cancel `EB'` in the normalized `X` equation.
  have hXk : X = EA' * k := by
    apply mul_left_cancel₀ hEB'ne
    calc
      EB' * X = EA' * C := hXeq'
      _ = EA' * (EB' * k) := by rw [hkC]
      _ = EB' * (EA' * k) := by ring

  -- The common factor `k` divides `Y` directly from `Y = n*C = n*EB'*k`.
  have hYk : Y = (n * EB') * k := by
    calc
      Y = n * C := hYC
      _ = n * (EB' * k) := by rw [hkC]
      _ = (n * EB') * k := by ring

  have hkUnit : IsUnit k :=
    isUnit_of_coprime_scaled hXY hXk hYk
  have hk1 : k = 1 := positive_unit_eq_one hkpos hkUnit

  have hCfinal : C = EB' := by
    simpa [hk1] using hkC

  have hXfinal : 3 * X = eisensteinEA m n := by
    calc
      3 * X = 3 * (EA' * k) := by rw [hXk]
      _ = 3 * EA' := by
        rw [hk1]
        ring
      _ = eisensteinEA m n := hEA.symm

  -- Cancel `EB'` in the `Y` scale equation to get `3*Y = EC*k`.
  have hYeq3 : (3 * EB') * Y = (2 * m * n - n ^ 2) * C := by
    simpa [hEB] using hYeq
  have hYscaled : 3 * Y = (2 * m * n - n ^ 2) * k := by
    apply mul_left_cancel₀ hEB'ne
    calc
      EB' * (3 * Y) = (3 * EB') * Y := by ring
      _ = (2 * m * n - n ^ 2) * C := hYeq3
      _ = (2 * m * n - n ^ 2) * (EB' * k) := by rw [hkC]
      _ = EB' * ((2 * m * n - n ^ 2) * k) := by ring
  have hYfinal : 3 * Y = 2 * m * n - n ^ 2 := by
    simpa [hk1] using hYscaled

  -- Same cancellation for `Z`.
  have hZeq3 : (3 * EB') * Z = (m ^ 2 - m * n + n ^ 2) * C := by
    simpa [hEB] using hZeq
  have hZscaled : 3 * Z = (m ^ 2 - m * n + n ^ 2) * k := by
    apply mul_left_cancel₀ hEB'ne
    calc
      EB' * (3 * Z) = (3 * EB') * Z := by ring
      _ = (m ^ 2 - m * n + n ^ 2) * C := hZeq3
      _ = (m ^ 2 - m * n + n ^ 2) * (EB' * k) := by rw [hkC]
      _ = EB' * ((m ^ 2 - m * n + n ^ 2) * k) := by ring
  have hZfinal : 3 * Z = m ^ 2 - m * n + n ^ 2 := by
    simpa [hk1] using hZscaled

  exact ⟨hCfinal, hXfinal, hYfinal, hZfinal⟩

end MazurProof.RationalPointsN12
```

API notes: `isUnit_of_coprime_scaled` is the common-scale helper; it uses only `hXY.isUnit_of_dvd'`. The theorem never introduces integer division: `C = EB' * k` comes from Euclid, and the `Y`/`Z` equations are obtained by cancelling the nonzero factor `EB'` with `mul_left_cancel₀`.
