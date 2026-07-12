import FLT.Assumptions.MazurProof.N18RouteC_FieldArithmetic
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# The inert valuation above two

This is the second fixed valuation used by the three-descent.  In particular,
its value on `2` rules out the two nontrivial special Kummer values as actual
cubes in `L`.
-/

namespace MazurProof.N18RouteC.TwoAdic

open FieldArithmetic

noncomputable section

abbrev OL := NumberField.RingOfIntegers L

theorem primeAboveTwo_isPrime : primeAboveTwo.IsPrime := primeAboveTwo_mem.1

theorem primeAboveTwo_ne_bot : primeAboveTwo ≠ ⊥ := by
  rw [primeAboveTwo_eq_span_two, ne_eq, Ideal.span_singleton_eq_bot]
  norm_num

def p2 : IsDedekindDomain.HeightOneSpectrum OL where
  asIdeal := primeAboveTwo
  isPrime := primeAboveTwo_isPrime
  ne_bot := primeAboveTwo_ne_bot

def v2 := p2.valuation L

def ordTwo (x : L) : ℤ := -WithZero.log (v2 x)

theorem v2_two : v2 (2 : L) = WithZero.exp (-1 : ℤ) := by
  rw [v2, ← show (((2 : OL) : L)) = (2 : L) by rfl,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  apply IsDedekindDomain.HeightOneSpectrum.intValuation_singleton
  · norm_num
  · exact primeAboveTwo_eq_span_two

theorem ordTwo_two : ordTwo (2 : L) = 1 := by
  simp [ordTwo, v2_two]

private theorem v2_ne_zero {x : L} (hx : x ≠ 0) : v2 x ≠ 0 :=
  (Valuation.ne_zero_iff v2).2 hx

theorem half_not_cube (c : L) : c ^ 3 ≠ (1 / 2 : L) := by
  intro hcub
  have hc : c ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by norm_num : (3 : ℕ) ≠ 0)] at hcub
    norm_num at hcub
  have hv := congrArg v2 hcub
  rw [map_pow, map_div₀, map_one, v2_two] at hv
  have hlog := congrArg WithZero.log hv
  rw [WithZero.log_pow] at hlog
  simp at hlog
  omega

theorem negTwo_not_cube (c : L) : c ^ 3 ≠ (-2 : L) := by
  intro hcub
  have hc : c ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by norm_num : (3 : ℕ) ≠ 0)] at hcub
    norm_num at hcub
  have hv := congrArg v2 hcub
  rw [map_pow, v2.map_neg, v2_two] at hv
  have hlog := congrArg WithZero.log hv
  rw [WithZero.log_pow] at hlog
  simp at hlog
  omega

end

end MazurProof.N18RouteC.TwoAdic
