```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein
import Mathlib.Algebra.Group.Int.Units
import Mathlib.RingTheory.PrincipalIdealDomain

namespace MazurProof.RationalPointsN12

theorem positive_unit_eq_one {k : ℤ} (hk : 0 < k) (hu : IsUnit k) :
    k = 1 := by
  rcases Int.isUnit_eq_one_or hu with h | h
  · exact h
  · have : (0 : ℤ) < -1 := by
      simpa [h] using hk
    norm_num at this

private theorem isUnit_of_common_scale {X Y A B k : ℤ}
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

theorem eisenstein_scale_kill_raw {X Y Z m n C : ℤ}
    (hXY : IsCoprime X Y)
    (hnpos : 0 < n) (hYpos : 0 < Y)
    (hEBpos : 0 < eisensteinEB m n)
    (hEAEB : IsCoprime (eisensteinEA m n) (eisensteinEB m n))
    (hZeq : eisensteinEB m n * Z = (m ^ 2 - m * n + n ^ 2) * C)
    (hXeq : eisensteinEB m n * X = eisensteinEA m n * C)
    (hYC : Y = n * C) :
    C = eisensteinEB m n ∧ X = eisensteinEA m n ∧
      Y = 2 * m * n - n ^ 2 ∧ Z = m ^ 2 - m * n + n ^ 2 := by
  have hEBne : eisensteinEB m n ≠ 0 := ne_of_gt hEBpos

  -- Euclid: from `EB * X = EA * C` and `IsCoprime EA EB`, get `EB ∣ C`.
  have hEB_dvd_EA_C : eisensteinEB m n ∣ eisensteinEA m n * C := by
    refine ⟨X, ?_⟩
    exact hXeq.symm
  have hEB_dvd_C : eisensteinEB m n ∣ C :=
    hEAEB.symm.dvd_of_dvd_mul_left hEB_dvd_EA_C
  rcases hEB_dvd_C with ⟨k, hkC⟩

  -- Positivity of the scale `k`.
  have hCpos : 0 < C := by
    have hprod : 0 < n * C := by
      simpa [hYC] using hYpos
    exact pos_of_mul_pos_left hprod (le_of_lt hnpos)
  have hkpos : 0 < k := by
    have hprod : 0 < eisensteinEB m n * k := by
      simpa [hkC] using hCpos
    exact pos_of_mul_pos_left hprod (le_of_lt hEBpos)

  -- Cancel `EB` to get the common scale on `X`.
  have hXk : X = eisensteinEA m n * k := by
    apply mul_left_cancel₀ hEBne
    calc
      eisensteinEB m n * X = eisensteinEA m n * C := hXeq
      _ = eisensteinEA m n * (eisensteinEB m n * k) := by rw [hkC]
      _ = eisensteinEB m n * (eisensteinEA m n * k) := by ring

  -- Use `Y = n*C` and `C = EB*k` to get the same scale on `Y`.
  have hYk : Y = (2 * m * n - n ^ 2) * k := by
    calc
      Y = n * C := hYC
      _ = n * (eisensteinEB m n * k) := by rw [hkC]
      _ = (2 * m * n - n ^ 2) * k := by
          unfold eisensteinEB
          ring

  -- No coprimality of `EA` and `2mn-n^2` is needed: `k` divides both `X` and `Y`.
  have hkUnit : IsUnit k :=
    isUnit_of_common_scale hXY hXk hYk
  have hk1 : k = 1 := positive_unit_eq_one hkpos hkUnit

  have hCfinal : C = eisensteinEB m n := by
    simpa [hk1] using hkC
  have hXfinal : X = eisensteinEA m n := by
    simpa [hk1] using hXk
  have hYfinal : Y = 2 * m * n - n ^ 2 := by
    simpa [hk1] using hYk

  -- Finally cancel `EB` in the `Z` equation after `C = EB`.
  have hZfinal : Z = m ^ 2 - m * n + n ^ 2 := by
    apply mul_left_cancel₀ hEBne
    calc
      eisensteinEB m n * Z = (m ^ 2 - m * n + n ^ 2) * C := hZeq
      _ = (m ^ 2 - m * n + n ^ 2) * eisensteinEB m n := by rw [hCfinal]
      _ = eisensteinEB m n * (m ^ 2 - m * n + n ^ 2) := by ring

  exact ⟨hCfinal, hXfinal, hYfinal, hZfinal⟩

end MazurProof.RationalPointsN12
```

API notes: `positive_unit_eq_one` uses `Int.isUnit_eq_one_or` from `Mathlib.Algebra.Group.Int.Units`. `isUnit_of_common_scale` is the requested minimal common-scale helper: it proves `IsUnit k` from `IsCoprime X Y`, `X = A*k`, and `Y = B*k`, with no `IsCoprime A B` hypothesis.
