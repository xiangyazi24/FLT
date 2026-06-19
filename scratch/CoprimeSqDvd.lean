import Mathlib

/-!
# THE LAST LEMMA: coprime product implies perfect square

From a²q = b²N with gcd(a,b)=1 and gcd(q,|N|)=1:
  q | b² (coprime q and N) AND b² | q (coprime a² and b²).
  So q = b². IsSquare q.
-/

theorem coprime_sq_dvd_implies_sq (q : ℕ) (b : ℕ) (a N : ℤ)
    (hab : Int.gcd a b = 1)
    (hqN : Nat.Coprime q N.natAbs)
    (heq : a ^ 2 * (q : ℤ) = (b : ℤ) ^ 2 * N) :
    IsSquare q := by
  have hq_dvd_b2 : q ∣ b ^ 2 := by
    have h : (q : ℤ) ∣ (b : ℤ) ^ 2 * N := ⟨a ^ 2, by linarith⟩
    have hcop : IsCoprime (q : ℤ) N := Int.isCoprime_iff_gcd_eq_one.mpr hqN
    exact_mod_cast hcop.dvd_of_dvd_mul_right h
  have hb2_dvd_q : b ^ 2 ∣ q := by
    have h : (b : ℤ) ^ 2 ∣ a ^ 2 * (q : ℤ) := ⟨N, by linarith⟩
    have hcop : IsCoprime (a ^ 2) ((b : ℤ) ^ 2) :=
      Int.isCoprime_iff_gcd_eq_one.mpr (Int.pow_gcd_pow_of_gcd_eq_one hab)
    exact_mod_cast hcop.symm.dvd_of_dvd_mul_left h
  exact ⟨b, (Nat.dvd_antisymm hq_dvd_b2 hb2_dvd_q).symm ▸ by ring⟩
