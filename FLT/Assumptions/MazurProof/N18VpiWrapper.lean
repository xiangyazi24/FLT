import FLT.Assumptions.MazurProof.N18RouteC_ThreeAdic
import FLT.Assumptions.MazurProof.N18AddCongr

/-!
# The additive valuation attached to the prime above three

This file packages `ordPi` as an honest additive valuation with values in
`WithTop ℤ`.  In particular, unlike `ordPi`, its value at zero is `⊤`.
-/

namespace MazurProof.N18RouteC.ThreeAdic

open FieldArithmetic
open MazurProof.N18Block5Instantiation.AddCongr
open scoped NumberField

noncomputable section

/-- The additive `pi`-adic valuation extending `ordPi`, with value `⊤` at zero. -/
def vpiGood : AddValuation L (WithTop ℤ) :=
  AddValuation.of
    (fun x ↦ if x = 0 then ⊤ else (ordPi x : WithTop ℤ))
    (by simp)
    (by simp [ordPi_one])
    (by
      intro x y
      by_cases hxy : x + y = 0
      · simp [hxy]
      by_cases hx : x = 0
      · simp [hx, hxy]
      by_cases hy : y = 0
      · simp [hy, hxy]
      simpa [hx, hy, hxy] using ordPi_add_ge hx hy hxy)
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      simp [hx, hy, ordPi_mul hx hy])

@[simp]
theorem vpiGood_apply_of_ne {x : L} (hx : x ≠ 0) :
    vpiGood x = (ordPi x : WithTop ℤ) := by
  simp [vpiGood, hx]

@[simp]
theorem vpiGood_zero : vpiGood (0 : L) = ⊤ := by
  exact vpiGood.map_zero

@[simp]
theorem vpiGood_one : vpiGood (1 : L) = 0 := by
  exact vpiGood.map_one

@[simp]
theorem vpiGood_three : vpiGood (3 : L) = (3 : WithTop ℤ) := by
  rw [vpiGood_apply_of_ne (by norm_num), ordPi_three]; norm_cast

@[simp]
theorem vpiGood_unit (m : ℤ) (hm : ¬ (3 ∣ m)) :
    vpiGood (m : L) = 0 := by
  have hm0 : m ≠ 0 := by
    intro h
    subst m
    exact hm (dvd_zero 3)
  have hm0L : (m : L) ≠ 0 := by
    exact_mod_cast hm0
  have hm_not_mem : (m : OL) ∉ primeAboveThree := by
    letI : primeAboveThree.LiesOver
        (Ideal.span ({(3 : ℤ)} : Set ℤ)) := primeAboveThree_mem.2
    intro hmem
    apply hm
    have hmem' : m ∈ Ideal.span ({(3 : ℤ)} : Set ℤ) := by
      rw [Ideal.mem_of_liesOver (P := primeAboveThree)]
      simpa using hmem
    rwa [Ideal.mem_span_singleton] at hmem'
  have hv3m : v3 (m : L) = 1 := by
    rw [v3, ← show (((m : OL) : L)) = (m : L) by norm_num,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
    exact hm_not_mem
  rw [vpiGood_apply_of_ne hm0L]
  simp [ordPi, hv3m]

end

end MazurProof.N18RouteC.ThreeAdic
