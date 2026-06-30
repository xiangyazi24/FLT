# Q2335: `QuarticAPrimitiveParitySplit`

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

-- Included only so this snippet checks standalone.  In the project file,
-- keep the existing definitions and paste only the two lemmas and theorem.
def QuarticA (u v Z : ℤ) : Prop :=
  Z ^ 2 = u ^ 4 + 2 * u ^ 2 * v ^ 2 - 3 * v ^ 4

def QuarticAPrimitiveParitySplit : Prop :=
  ∀ {u v Z : ℤ},
    Int.gcd u v = 1 →
    u * v ≠ 0 →
    QuarticA u v Z →
    (((Odd u ∧ Even v) ∨ (Even u ∧ Odd v)) ∨ (Odd u ∧ Odd v))

/-- If an integer is even, then its natural absolute value is divisible by `2`. -/
lemma quarticA_natAbs_two_dvd_of_even {z : ℤ} (hz : Even z) :
    (2 : ℕ) ∣ z.natAbs := by
  have h2z : (2 : ℤ) ∣ z := (even_iff_two_dvd.mp hz)
  rcases h2z with ⟨k, hk⟩
  refine ⟨k.natAbs, ?_⟩
  calc
    z.natAbs = ((2 : ℤ) * k).natAbs := by simpa [hk]
    _ = (2 : ℤ).natAbs * k.natAbs := by
      simpa using (Int.natAbs_mul (2 : ℤ) k)
    _ = 2 * k.natAbs := by norm_num

/-- A primitive integer pair cannot have both entries even. -/
lemma quarticA_not_even_even_of_int_gcd_eq_one {u v : ℤ}
    (hcop : Int.gcd u v = 1) :
    ¬ (Even u ∧ Even v) := by
  rintro ⟨hu, hv⟩
  have huNat : (2 : ℕ) ∣ u.natAbs := quarticA_natAbs_two_dvd_of_even hu
  have hvNat : (2 : ℕ) ∣ v.natAbs := quarticA_natAbs_two_dvd_of_even hv
  have hgNat : (2 : ℕ) ∣ Nat.gcd u.natAbs v.natAbs :=
    Nat.dvd_gcd huNat hvNat
  have hcopNat : Nat.gcd u.natAbs v.natAbs = 1 := by
    simpa [Int.gcd_eq_natAbs] using hcop
  rw [hcopNat] at hgNat
  norm_num at hgNat

theorem quarticAPrimitiveParitySplit : QuarticAPrimitiveParitySplit := by
  intro u v Z hcop _huv0 _hA
  rcases Int.even_or_odd u with huEven | huOdd
  · rcases Int.even_or_odd v with hvEven | hvOdd
    · exfalso
      exact quarticA_not_even_even_of_int_gcd_eq_one
        (u := u) (v := v) hcop ⟨huEven, hvEven⟩
    · exact Or.inl (Or.inr ⟨huEven, hvOdd⟩)
  · rcases Int.even_or_odd v with hvEven | hvOdd
    · exact Or.inl (Or.inl ⟨huOdd, hvEven⟩)
    · exact Or.inr ⟨huOdd, hvOdd⟩

end MazurProof.RationalPointsN12
```

Notes:

* `QuarticA` and `u * v ≠ 0` are not used.  The theorem is purely parity exhaustion plus `Int.gcd u v = 1`.
* The both-even contradiction is proved by passing from `Even z` to `(2 : ℕ) ∣ z.natAbs`, then using `Nat.dvd_gcd` and `Int.gcd_eq_natAbs` to contradict `Int.gcd u v = 1`.
* If the local Mathlib exposes `Int.gcd` by definitional unfolding rather than the rewrite theorem, replace
  ```lean
  simpa [Int.gcd_eq_natAbs] using hcop
  ```
  with
  ```lean
  simpa [Int.gcd] using hcop
  ```
  in `quarticA_not_even_even_of_int_gcd_eq_one`.
* If an older local file does not have the global theorem `even_iff_two_dvd` in scope, the intended replacement is the same first step by definition/witness expansion: obtain `⟨k, hk⟩ : (2 : ℤ) ∣ z`, then finish with `Int.natAbs_mul` exactly as above.
