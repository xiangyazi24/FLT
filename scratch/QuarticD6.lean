import Mathlib

/-!
# The `d = 6` quartic obstruction

We prove that no integer `t` can satisfy

` s^4 + 36*s^2 - 1296 = t^2 `

when `s` is coprime to `6`.  The Lean statement records this as the two
conditions `¬ 2 ∣ s` and `¬ 3 ∣ s`; only oddness is needed for the proof.
-/

namespace Scratch.ChatGPTDropDM1

/--
For integers `s` coprime to `6`, the value
`s^4 + 36*s^2 - 1296` is never an integer square.
-/
theorem quartic_no_sol_d6 (s t : ℤ)
    (hs_odd : ¬ (2 : ℤ) ∣ s)
    (_hs_not_three : ¬ (3 : ℤ) ∣ s) :
    s ^ 4 + 36 * s ^ 2 - 1296 = t ^ 2 → False := by
  intro h
  rcases Int.even_or_odd s with hs_even | hs_odd_s
  · rcases hs_even with ⟨c, hc⟩
    exact hs_odd ⟨c, by rw [hc]; ring⟩
  · rcases hs_odd_s with ⟨c, hc⟩
    rcases Int.even_or_odd t with ht_even | ht_odd_t
    · rcases ht_even with ⟨d, hd⟩
      rw [hc, hd] at h
      ring_nf at h
      omega
    · rcases ht_odd_t with ⟨d, hd⟩
      rcases Int.even_or_odd d with hd_even | hd_odd
      · rcases hd_even with ⟨e, he⟩
        rw [hc, hd, he] at h
        ring_nf at h
        omega
      · rcases hd_odd with ⟨e, he⟩
        rw [hc, hd, he] at h
        ring_nf at h
        omega

end Scratch.ChatGPTDropDM1
