# Quartic `d = 10` no-square proof

The goal is to prove that

\[
s^4 + 100s^2 - 10000 = t^2
\]

has no integer solutions when `gcd(s,10)=1`.  I state this in Lean as the two hypotheses `¬ (2 : ℤ) ∣ s` and `¬ (5 : ℤ) ∣ s`; only oddness is needed for the contradiction.

The key congruence is modulo `8`.  If `s` is odd, then `s^2 ≡ 1 (mod 8)` and `s^4 ≡ 1 (mod 8)`.  Also `100s^2 ≡ 4 (mod 8)` and `10000 ≡ 0 (mod 8)`, so

\[
s^4 + 100s^2 - 10000 \equiv 5 \pmod 8.
\]

No square is congruent to `5` modulo `8`.  The proof below follows the requested parity-split style.  Importantly, `Int.even_or_odd` is used in its actual form: the even witness is `s = c + c`, and the odd witness is `s = c + c + 1`; the proof never assumes a witness of the form `2*c` directly.

```lean
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
```
