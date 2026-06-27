# Q1482 (dm1/dm3): `UV_coprime` prime-divisor proof

Below is the replacement proof I would use.  It proves `IsCoprime U V` by contradiction after converting to `Nat.Coprime U.natAbs V.natAbs`, then extracts a common prime divisor via

```lean
Nat.Prime.not_coprime_iff_dvd
```

This is the Lean-clean version of “gcd is bigger than `1`, so choose a prime divisor of the gcd.”

The only local dependency is your existing

```lean
UV_odd : ... →
  (2 * r ^ 2 + B ^ 2 - 2 * s) % 2 = 1 ∧
  (2 * r ^ 2 + B ^ 2 + 2 * s) % 2 = 1
```

If your local `UV_odd` has hypotheses in a slightly different order, only the single line defining `hUVodd` needs adjustment.

```lean
import Mathlib

namespace DM3

/-- Coprimality of the two quartic descent factors in the odd case. -/
theorem UV_coprime {r B s : ℤ} (hr : 0 < r) (hB : 0 < B)
    (hcop : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4)
    (hr_odd : r % 2 = 1) (hB_odd : B % 2 = 1) :
    Int.gcd (2 * r ^ 2 + B ^ 2 - 2 * s)
      (2 * r ^ 2 + B ^ 2 + 2 * s) = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one]

  let A : ℤ := 2 * r ^ 2 + B ^ 2
  let U : ℤ := A - 2 * s
  let V : ℤ := A + 2 * s

  have hA_sq_sub : A ^ 2 - 4 * s ^ 2 = 5 * B ^ 4 := by
    dsimp [A]
    nlinarith [heq]

  -- Existing local lemma: both factors are odd in the odd-odd case.
  have hUVodd := UV_odd (r := r) (B := B) (s := s) hr_odd hB_odd
  have hUodd : U % 2 = 1 := by
    simpa [U, A] using hUVodd.1

  -- Work with `Nat.Coprime` on absolute values, then use the prime-divisor criterion.
  rw [Int.isCoprime_iff_nat_coprime]
  by_contra hnot
  rcases Nat.Prime.not_coprime_iff_dvd.mp hnot with
    ⟨p, hp, hpU_nat, hpV_nat⟩

  have hpU : (p : ℤ) ∣ U := Int.natCast_dvd.mpr hpU_nat
  have hpV : (p : ℤ) ∣ V := Int.natCast_dvd.mpr hpV_nat

  -- The common prime is not `2`, since it divides the odd factor `U`.
  have hp_ne_two : p ≠ 2 := by
    intro hp2
    have h2U : (2 : ℤ) ∣ U := by
      simpa [hp2] using hpU
    have hUmod0 : U % 2 = 0 := by
      exact Int.dvd_iff_emod_eq_zero.mp h2U
    omega

  have hp_odd_nat : Odd p := hp.odd_of_ne_two hp_ne_two
  have hp_coprime2_nat : Nat.Coprime p 2 := by
    simpa using (Nat.coprime_two_right.mpr hp_odd_nat)
  have hp_coprime2 : IsCoprime (p : ℤ) (2 : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hp_coprime2_nat
  have hp_coprime4 : IsCoprime (p : ℤ) ((2 : ℤ) ^ 2) :=
    hp_coprime2.pow_right (n := 2)

  -- From common divisibility, get `p ∣ s` and `p ∣ A`.
  have hp4s : (p : ℤ) ∣ 4 * s := by
    have h : (p : ℤ) ∣ V - U := dvd_sub hpV hpU
    have hsub : V - U = 4 * s := by
      dsimp [U, V, A]
      ring
    simpa [hsub] using h

  have hp2A : (p : ℤ) ∣ 2 * A := by
    have h : (p : ℤ) ∣ V + U := dvd_add hpV hpU
    have hadd : V + U = 2 * A := by
      dsimp [U, V, A]
      ring
    simpa [hadd] using h

  have hps : (p : ℤ) ∣ s := by
    apply hp_coprime4.dvd_of_dvd_mul_right
    simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hp4s

  have hpA : (p : ℤ) ∣ A := by
    apply hp_coprime2.dvd_of_dvd_mul_right
    simpa [mul_assoc, mul_comm, mul_left_comm] using hp2A

  -- Hence `p^2 ∣ A^2 - 4*s^2 = 5*B^4`.
  have hp2_A2 : (p : ℤ) ^ 2 ∣ A ^ 2 := by
    exact pow_dvd_pow_of_dvd hpA 2
  have hp2_s2 : (p : ℤ) ^ 2 ∣ s ^ 2 := by
    exact pow_dvd_pow_of_dvd hps 2
  have hp2_4s2 : (p : ℤ) ^ 2 ∣ 4 * s ^ 2 :=
    dvd_mul_of_dvd_right hp2_s2 4
  have hp2_expr : (p : ℤ) ^ 2 ∣ A ^ 2 - 4 * s ^ 2 :=
    dvd_sub hp2_A2 hp2_4s2
  have hp2_5B4 : (p : ℤ) ^ 2 ∣ 5 * B ^ 4 := by
    simpa [hA_sq_sub] using hp2_expr

  -- Coprimality of the original primitive pair, as natural coprimality.
  have hcopNat : Nat.Coprime r.natAbs B.natAbs := by
    rw [Nat.coprime_iff_gcd_eq_one]
    simpa [Int.gcd_eq_natAbs] using hcop

  by_cases hpB_nat : p ∣ B.natAbs
  · -- If `p ∣ B`, then `p ∣ r`, contradiction to `gcd(r,B)=1`.
    have hpB : (p : ℤ) ∣ B := Int.natCast_dvd.mpr hpB_nat
    have hpB2 : (p : ℤ) ∣ B ^ 2 := pow_dvd_pow_of_dvd hpB 2
    have hp_two_r2 : (p : ℤ) ∣ 2 * r ^ 2 := by
      have h : (p : ℤ) ∣ A - B ^ 2 := dvd_sub hpA hpB2
      simpa [A] using h
    have hpr_or :=
      prime_two_or_dvd_of_dvd_two_mul_pow_self_two (m := r) hp
        (by simpa [pow_two] using hp_two_r2)
    rcases hpr_or with hp2 | hpr_nat
    · exact hp_ne_two hp2
    · have hp_one : p = 1 :=
        Nat.eq_one_of_dvd_coprimes hcopNat hpr_nat hpB_nat
      exact hp.ne_one hp_one
  · -- If `p ∤ B`, then `p^2` is coprime to `B^4`, so `p^2 ∣ 5`, impossible.
    have hcop_p_B_nat : Nat.Coprime p B.natAbs := by
      by_contra hpc
      exact hpB_nat ((hp.dvd_iff_not_coprime).mpr hpc)
    have hcop_p_B : IsCoprime (p : ℤ) B := by
      rw [Int.isCoprime_iff_nat_coprime]
      simpa using hcop_p_B_nat
    have hcop_p2_B4 : IsCoprime ((p : ℤ) ^ 2) (B ^ 4) := by
      simpa using (hcop_p_B.pow (m := 2) (n := 4))
    have hp2_dvd_5 : (p : ℤ) ^ 2 ∣ (5 : ℤ) :=
      hcop_p2_B4.dvd_of_dvd_mul_right hp2_5B4
    have hp2_dvd_5_nat : p ^ 2 ∣ 5 := by
      have h : ((p ^ 2 : ℕ) : ℤ) ∣ (5 : ℤ) := by
        simpa [Int.natCast_pow] using hp2_dvd_5
      exact Int.natCast_dvd.mp h
    have hp_ge_three : 3 ≤ p := by
      have hp_two_le : 2 ≤ p := hp.two_le
      omega
    have hp_sq_ge_nine : 9 ≤ p ^ 2 := by
      nlinarith
    have hp_sq_le_five : p ^ 2 ≤ 5 :=
      Nat.le_of_dvd (by norm_num) hp2_dvd_5_nat
    omega

end DM3
```

Two practical notes:

1. If your local file already opened a namespace and defines `UV_coprime` there, remove `namespace DM3`/`end DM3`.
2. If your `UV_odd` theorem takes `hr_odd`/`hB_odd` in a different order, the only line to edit is:

```lean
have hUVodd := UV_odd (r := r) (B := B) (s := s) hr_odd hB_odd
```

The proof avoids manually reasoning about `Int.gcd > 1`; `Nat.Prime.not_coprime_iff_dvd` is exactly the same prime-extraction step, but after `Int.isCoprime_iff_nat_coprime` it gives the common prime divisor in the form Lean wants.