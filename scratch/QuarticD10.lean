import Mathlib

/-!
# The `d = 10` quartic obstruction

We prove that no integer `t` can satisfy

` s^4 + 100*s^2 - 10000 = t^2 `

when `s` is coprime to `10`.  The Lean statement records this as the two
conditions `¬ 2 ∣ s` and `¬ 5 ∣ s`; only oddness is needed.
-/

namespace Scratch.ChatGPTDropDM1

/--
For integers `s` coprime to `10`, the value
`s^4 + 100*s^2 - 10000` is never an integer square.
-/
theorem quartic_no_sol_d10 (s t : ℤ)
    (hs_odd : ¬ (2 : ℤ) ∣ s)
    (_hs_not_five : ¬ (5 : ℤ) ∣ s) :
    s ^ 4 + 100 * s ^ 2 - 10000 = t ^ 2 → False := by
  intro h
  rcases Int.even_or_odd s with hs_even | hs_odd_s
  · rcases hs_even with ⟨c, hc⟩
    exact hs_odd ⟨c, by rw [hc]; ring⟩
  · rcases hs_odd_s with ⟨a, ha⟩
    rcases Int.even_or_odd t with ht_even | ht_odd_t
    · rcases ht_even with ⟨d, hd⟩
      rw [ha, hd] at h
      ring_nf at h
      omega
    · rcases ht_odd_t with ⟨d, hd⟩
      rcases Int.even_or_odd d with hd_even | hd_odd
      · rcases hd_even with ⟨e, he⟩
        rw [ha, hd, he] at h
        ring_nf at h
        omega
      · rcases hd_odd with ⟨e, he⟩
        rw [ha, hd, he] at h
        ring_nf at h
        omega

end Scratch.ChatGPTDropDM1
