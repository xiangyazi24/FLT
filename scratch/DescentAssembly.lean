import Mathlib
import FLT.Assumptions.MazurProof.DescentBridge

namespace MazurProof

private theorem cover_no_sol_prime (p d u v : ℤ) (hp : Prime p) (hpd : p ∣ d)
    (h : d * v ^ 2 = d ^ 2 * u ^ 4 + d * u ^ 2 - 1) : False := by
  rcases hpd with ⟨k, rfl⟩
  have : p ∣ (1 : ℤ) := ⟨p * k ^ 2 * u ^ 4 + k * u ^ 2 - k * v ^ 2, by nlinarith⟩
  exact hp.not_dvd_one this

theorem cover_forces_unit (d u v : ℤ) (hd : d ≠ 0)
    (h : d * v ^ 2 = d ^ 2 * u ^ 4 + d * u ^ 2 - 1) :
    d = 1 ∨ d = -1 := by
  by_contra habs
  push Not at habs
  obtain ⟨h1, hm1⟩ := habs
  have hna : d.natAbs ≠ 1 := by
    intro heq
    rcases Int.natAbs_eq d with h | h <;> omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hna
  have hpd_int : (p : ℤ) ∣ d := by
    have := Int.natCast_dvd_natCast.mpr hpd
    exact Int.dvd_natAbs.mp this
  exact cover_no_sol_prime (↑p) d u v (Nat.prime_iff_prime_int.mp hp) hpd_int h

end MazurProof
