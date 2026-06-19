import Mathlib

namespace DenominatorQuartic

/-- The positive denominator quartic. -/
def PosQuartic (p q t : ℤ) : Prop :=
  t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4

/-- The smaller-solution output used by descent. -/
def SmallerSolution (p q t p' q' t' : ℤ) : Prop :=
  2 ≤ q' ∧
  Int.gcd p' q' = 1 ∧
  PosQuartic p' q' t' ∧
  q'.natAbs < q.natAbs

private lemma natAbs_lt_of_nonneg_of_lt {a q : ℤ}
    (ha : 0 ≤ a) (hq : 0 ≤ q) (h : a < q) :
    a.natAbs < q.natAbs := by
  omega

private lemma posQuartic_of_coeff_eq (c d n : ℤ)
    (h : n ^ 2 = d ^ 4 + d ^ 2 * c ^ 2 - c ^ 4) :
    PosQuartic d c n := by
  unfold PosQuartic
  nlinarith

/--
Algebraic tail after the two `Int.sq_of_isCoprime` splits.

The two splits should have produced:

* `p-r = c⁴`,
* `p+r = d⁴`,
* `m = c*d`,
* `2r = n²-m²`,
* `gcd(d,c)=1`.

Then `(p',q',t')=(d,c,n)` satisfies the same quartic and has smaller
denominator.
-/
theorem pythagorean_descent_tail_from_fourth_split
    (p q t m n r c d : ℤ)
    (hc : 2 ≤ c)
    (hd : 1 ≤ d)
    (hn : 1 ≤ n)
    (hm_lt_q : m < q)
    (hq_nonneg : 0 ≤ q)
    (hcop_dc : Int.gcd d c = 1)
    (hpc : p - r = c ^ 4)
    (hpd : p + r = d ^ 4)
    (hm : m = c * d)
    (hr : 2 * r = n ^ 2 - m ^ 2) :
    ∃ p' q' t' : ℤ, SmallerSolution p q t p' q' t' := by
  have hn_eq : n ^ 2 = d ^ 4 + d ^ 2 * c ^ 2 - c ^ 4 := by
    nlinarith
  refine ⟨d, c, n, ?_⟩
  constructor
  · exact hc
  constructor
  · exact hcop_dc
  constructor
  · exact posQuartic_of_coeff_eq c d n hn_eq
  · have hc_nonneg : 0 ≤ c := by omega
    have hc_le_m : c ≤ m := by nlinarith
    have hc_lt_q : c < q := by omega
    exact natAbs_lt_of_nonneg_of_lt hc_nonneg hq_nonneg hc_lt_q

end DenominatorQuartic
