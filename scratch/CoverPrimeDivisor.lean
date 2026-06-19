import Mathlib

/-!
# Prime-divisor obstruction for the `20.a4` 2-isogeny cover

For the cover

`d * v^2 = d^2 * u^4 + d * u^2 - 1`,

any prime divisor of `d` gives an immediate contradiction: reducing modulo that
prime gives `0 = -1`.
-/

namespace Scratch.ChatGPTDropDM1

/--
If a prime `p` divides `d`, then the homogeneous space
`d * v² = d² * u⁴ + d * u² - 1` has no integer point.
-/
theorem cover_no_solution_of_prime_dvd
    (p d u v : ℤ)
    (hp : Prime p)
    (_hp_ge_two : (2 : ℤ) ≤ p)
    (hpd : p ∣ d)
    (h : d * v ^ 2 = d ^ 2 * u ^ 4 + d * u ^ 2 - 1) :
    False := by
  rcases hpd with ⟨k, rfl⟩
  have hp_dvd_one : p ∣ (1 : ℤ) := by
    refine ⟨p * k ^ 2 * u ^ 4 + k * u ^ 2 - k * v ^ 2, ?_⟩
    calc
      (1 : ℤ) = (p * k) ^ 2 * u ^ 4 + (p * k) * u ^ 2 - (p * k) * v ^ 2 := by
        nlinarith
      _ = p * (p * k ^ 2 * u ^ 4 + k * u ^ 2 - k * v ^ 2) := by
        ring
  exact hp.not_dvd_one hp_dvd_one

end Scratch.ChatGPTDropDM1
