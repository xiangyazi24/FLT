```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein
import Mathlib.RingTheory.PrincipalIdealDomain

namespace MazurProof.RationalPointsN12

private theorem three_mul_dvd_three_mul_of_dvd {d a : ℤ}
    (h : d ∣ a) :
    3 * d ∣ 3 * a := by
  rcases h with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [hk]
  ring

private theorem isUnit_of_three_mul_dvd_three {d : ℤ}
    (h : 3 * d ∣ (3 : ℤ)) :
    IsUnit d := by
  rcases h with ⟨k, hk⟩
  have hcancel : (1 : ℤ) = d * k := by
    apply mul_left_cancel₀ (show (3 : ℤ) ≠ 0 by decide)
    calc
      (3 : ℤ) * 1 = 3 := by ring
      _ = (3 * d) * k := hk
      _ = 3 * (d * k) := by ring
  exact IsUnit.of_mul_eq_one k hcancel.symm

theorem eisenstein_factor_coprime_divided_witness {m n EA' EB' : ℤ}
    (hmn : IsCoprime m n)
    (hEA : eisensteinEA m n = 3 * EA')
    (hEB : eisensteinEB m n = 3 * EB') :
    IsCoprime EA' EB' := by
  apply IsRelPrime.isCoprime
  intro d hdA hdB
  have hdEA3' : 3 * d ∣ 3 * EA' :=
    three_mul_dvd_three_mul_of_dvd hdA
  have hdEB3' : 3 * d ∣ 3 * EB' :=
    three_mul_dvd_three_mul_of_dvd hdB
  have hdEA : 3 * d ∣ eisensteinEA m n := by
    simpa [hEA] using hdEA3'
  have hdEB : 3 * d ∣ eisensteinEB m n := by
    simpa [hEB] using hdEB3'
  have hd3 : 3 * d ∣ (3 : ℤ) :=
    eisenstein_common_dvd_three (d := 3 * d) (m := m) (n := n)
      hmn hdEA hdEB
  exact isUnit_of_three_mul_dvd_three hd3

end MazurProof.RationalPointsN12
```

API notes: `IsRelPrime.isCoprime` comes from `Mathlib.RingTheory.PrincipalIdealDomain`. The cancellation step is the local helper `isUnit_of_three_mul_dvd_three`: it rewrites `(3*d) ∣ 3` as `3 = (3*d)*k`, cancels the nonzero left factor `3` with `mul_left_cancel₀`, gets `1 = d*k`, and returns `IsUnit.of_mul_eq_one k`.
