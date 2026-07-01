```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein
import Mathlib.RingTheory.PrincipalIdealDomain

namespace MazurProof.RationalPointsN12

private abbrev EA (m n : ℤ) : ℤ := m ^ 2 - n ^ 2
private abbrev EB (m n : ℤ) : ℤ := 2 * m - n

theorem eisenstein_common_divisor_identity (m n : ℤ) :
    (2 * m + n) * EB m n - EA m n = 3 * m ^ 2 := by
  unfold EA EB
  ring

theorem eisenstein_common_divisor_coprime_m {d m n : ℤ}
    (hmn : IsCoprime m n) (hdB : d ∣ EB m n) :
    IsCoprime d m := by
  apply IsRelPrime.isCoprime
  intro c hcd hcm
  have hcB : c ∣ EB m n := hcd.trans hdB
  have hc2m : c ∣ 2 * m := hcm.mul_left 2
  have hcn : c ∣ n := by
    have htmp : c ∣ 2 * m - EB m n := dvd_sub hc2m hcB
    convert htmp using 1
    unfold EB
    ring
  exact hmn.isUnit_of_dvd' hcm hcn

theorem eisenstein_common_dvd_three {d m n : ℤ}
    (hmn : IsCoprime m n)
    (hdA : d ∣ EA m n) (hdB : d ∣ EB m n) :
    d ∣ (3 : ℤ) := by
  have hdm : IsCoprime d m :=
    eisenstein_common_divisor_coprime_m hmn hdB
  have hdCombo : d ∣ (2 * m + n) * EB m n - EA m n :=
    dvd_sub (hdB.mul_left (2 * m + n)) hdA
  have hd3m2 : d ∣ 3 * m ^ 2 := by
    simpa [eisenstein_common_divisor_identity m n] using hdCombo
  have hd3m : d ∣ 3 * m := by
    apply hdm.dvd_of_dvd_mul_left
    convert hd3m2 using 1
    ring
  exact hdm.dvd_of_dvd_mul_left (by
    convert hd3m using 1
    ring)

end MazurProof.RationalPointsN12
```

API notes: `IsRelPrime.isCoprime` is used only to build `IsCoprime d m` from the common-divisor criterion. The second lemma removes the two factors of `m` by applying `IsCoprime.dvd_of_dvd_mul_left` twice, so it avoids any `pow` coprimality API.
