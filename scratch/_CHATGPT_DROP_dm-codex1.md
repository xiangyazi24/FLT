```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein
import Mathlib.Algebra.Group.Int.Units
import Mathlib.RingTheory.PrincipalIdealDomain

namespace MazurProof.RationalPointsN12

theorem int_isUnit_or_three_dvd_of_dvd_three {d : ℤ}
    (hd : d ∣ (3 : ℤ)) : IsUnit d ∨ (3 : ℤ) ∣ d := by
  have hdNat : d.natAbs ∣ (3 : ℕ) := by
    rcases hd with ⟨k, hk⟩
    refine ⟨k.natAbs, ?_⟩
    have h := congrArg Int.natAbs hk
    simpa [Int.natAbs_mul] using h
  have hcase : d.natAbs = 1 ∨ d.natAbs = 3 :=
    Nat.prime_three.eq_one_or_self_of_dvd d.natAbs hdNat
  rcases hcase with hd1 | hd3
  · left
    exact Int.isUnit_iff_natAbs_eq.mpr hd1
  · right
    rw [← Int.dvd_natAbs, hd3]
    norm_num

theorem eisenstein_factor_coprime_raw {m n : ℤ}
    (hmn : IsCoprime m n)
    (h3 : ¬ (3 : ℤ) ∣ m + n) :
    IsCoprime (eisensteinEA m n) (eisensteinEB m n) := by
  apply IsRelPrime.isCoprime
  intro d hdA hdB
  have hd3 : d ∣ (3 : ℤ) :=
    eisenstein_common_dvd_three hmn hdA hdB
  rcases int_isUnit_or_three_dvd_of_dvd_three hd3 with hdUnit | hthree_d
  · exact hdUnit
  · have hthree_B : (3 : ℤ) ∣ eisensteinEB m n := hthree_d.trans hdB
    have hthree_sum : (3 : ℤ) ∣ m + n :=
      (eisenstein_EB_three_dvd_iff (m := m) (n := n)).mp hthree_B
    exact False.elim (h3 hthree_sum)

end MazurProof.RationalPointsN12
```

API notes: `Mathlib.Algebra.Group.Int.Units` provides `Int.isUnit_iff_natAbs_eq`; `Mathlib.RingTheory.PrincipalIdealDomain` provides `IsRelPrime.isCoprime`. If these are already imported by the local WIP file, the two extra imports can be dropped.
