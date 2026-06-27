# Q1412 (dm1): gcd of the two quartic factors

Here is the clean Lean architecture for the requested lemma.

The proof below uses `Int.Prime.dvd_mul'` and `Int.Prime.dvd_pow'` for the integer prime-divisibility steps.  I state the core theorem with `Odd r`/`Odd B`, and then give the exact wrapper for hypotheses `r % 2 = 1`, `B % 2 = 1`.

Important: the hypothesis `Int.gcd r B = 1` must be present.  It is used exactly in the subclaim `p ∣ B → p ∣ r`, contradiction.

```lean
import Mathlib

namespace DM1

abbrev U (r B s : ℤ) : ℤ := 2 * r ^ 2 + B ^ 2 - 2 * s
abbrev V (r B s : ℤ) : ℤ := 2 * r ^ 2 + B ^ 2 + 2 * s

lemma odd_of_emod_two_eq_one {z : ℤ} (hz : z % 2 = 1) : Odd z := by
  obtain ⟨k, hk⟩ := exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hz)
  rw [sub_eq_iff_eq_add] at hk
  exact ⟨k, by simpa [mul_comm] using hk⟩

lemma not_two_dvd_of_odd {z : ℤ} (hz : Odd z) : ¬ (2 : ℤ) ∣ z := by
  rintro ⟨k, hk⟩
  rcases hz with ⟨l, hl⟩
  omega

lemma U_odd_of_B_odd {r B s : ℤ} (hBodd : Odd B) : Odd (U r B s) := by
  rcases hBodd with ⟨b0, rfl⟩
  refine ⟨r ^ 2 + 2 * b0 ^ 2 + 2 * b0 - s, ?_⟩
  dsimp [U]
  ring

lemma V_odd_of_B_odd {r B s : ℤ} (hBodd : Odd B) : Odd (V r B s) := by
  rcases hBodd with ⟨b0, rfl⟩
  refine ⟨r ^ 2 + 2 * b0 ^ 2 + 2 * b0 + s, ?_⟩
  dsimp [V]
  ring

lemma prime_dvd_two_eq_two {p : ℕ} (hp : Nat.Prime p)
    (h : (p : ℤ) ∣ (2 : ℤ)) : p = 2 := by
  have hnat : p ∣ 2 := Int.natCast_dvd.mp h
  exact le_antisymm (Nat.le_of_dvd (by decide : 0 < 2) hnat) hp.two_le

lemma prime_dvd_five_eq_five {p : ℕ} (hp : Nat.Prime p)
    (h : (p : ℤ) ∣ (5 : ℤ)) : p = 5 := by
  have hnat : p ∣ 5 := Int.natCast_dvd.mp h
  have hp_le : p ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) hnat
  have hp_ge : 2 ≤ p := hp.two_le
  interval_cases p <;> norm_num at hnat hp ⊢

lemma prime_dvd_two_mul_right {p : ℕ} {x : ℤ}
    (hp : Nat.Prime p) (hpne : p ≠ 2)
    (h : (p : ℤ) ∣ 2 * x) :
    (p : ℤ) ∣ x := by
  rcases Int.Prime.dvd_mul' hp h with hp2 | hpx
  · exact False.elim (hpne (prime_dvd_two_eq_two hp hp2))
  · exact hpx

lemma quartic_UV_product
    {r B s : ℤ}
    (hs : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    U r B s * V r B s = 5 * B ^ 4 := by
  calc
    U r B s * V r B s = (2 * r ^ 2 + B ^ 2) ^ 2 - (2 * s) ^ 2 := by
      dsimp [U, V]
      ring
    _ = 5 * B ^ 4 := by
      rw [hs]
      ring

/-- Core prime-divisor exclusion: no natural prime can divide both factors. -/
lemma quartic_common_prime_UV_false
    {r B s : ℤ} {p : ℕ}
    (hp : Nat.Prime p)
    (hpU : (p : ℤ) ∣ U r B s)
    (hpV : (p : ℤ) ∣ V r B s)
    (_hrodd : Odd r)
    (hBodd : Odd B)
    (hcop : Int.gcd r B = 1)
    (hs : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    False := by
  have hUodd : Odd (U r B s) := U_odd_of_B_odd hBodd

  have hpne2 : p ≠ 2 := by
    intro hp2
    have h2U : (2 : ℤ) ∣ U r B s := by
      simpa [hp2] using hpU
    exact (not_two_dvd_of_odd hUodd) h2U

  -- From `p ∣ V + U = 2 * (2*r^2 + B^2)` and `p ≠ 2`, get
  -- `p ∣ 2*r^2 + B^2`.
  have hp_sum_raw : (p : ℤ) ∣ V r B s + U r B s := dvd_add hpV hpU
  have hsum_eq : V r B s + U r B s = 2 * (2 * r ^ 2 + B ^ 2) := by
    dsimp [U, V]
    ring
  have hp_sum : (p : ℤ) ∣ 2 * (2 * r ^ 2 + B ^ 2) := by
    rwa [hsum_eq] at hp_sum_raw
  have hp_A : (p : ℤ) ∣ 2 * r ^ 2 + B ^ 2 :=
    prime_dvd_two_mul_right hp hpne2 hp_sum

  -- Subclaim: `p ∤ B`; otherwise `p ∣ 2*r^2`, hence `p ∣ r`, contradicting
  -- `gcd r B = 1`.
  have hp_not_B : ¬ (p : ℤ) ∣ B := by
    intro hpB
    have hpB2 : (p : ℤ) ∣ B ^ 2 := by
      rw [sq]
      exact hpB.mul_right B
    have hp2r2_raw : (p : ℤ) ∣ (2 * r ^ 2 + B ^ 2) - B ^ 2 :=
      dvd_sub hp_A hpB2
    have hp2r2 : (p : ℤ) ∣ 2 * r ^ 2 := by
      have hsub_eq : (2 * r ^ 2 + B ^ 2) - B ^ 2 = 2 * r ^ 2 := by ring
      rwa [hsub_eq] at hp2r2_raw
    have hpr2 : (p : ℤ) ∣ r ^ 2 :=
      prime_dvd_two_mul_right hp hpne2 hp2r2
    have hpr : (p : ℤ) ∣ r := Int.Prime.dvd_pow' hp hpr2
    exact hp.not_dvd_one (by
      rw [← hcop]
      exact Nat.dvd_gcd (Int.natCast_dvd.mp hpr) (Int.natCast_dvd.mp hpB))

  have hUV : U r B s * V r B s = 5 * B ^ 4 := quartic_UV_product hs

  -- Since `p ∣ U*V = 5*B^4` and `p ∤ B`, primality forces `p = 5`.
  have hp_eq5 : p = 5 := by
    have hpUV_left : (p : ℤ) ∣ U r B s * V r B s := dvd_mul_of_dvd_left hpU _
    have hpUV : (p : ℤ) ∣ 5 * B ^ 4 := by
      rwa [hUV] at hpUV_left
    rcases Int.Prime.dvd_mul' hp hpUV with hp5 | hpB4
    · exact prime_dvd_five_eq_five hp hp5
    · exact False.elim (hp_not_B (Int.Prime.dvd_pow' hp hpB4))

  -- But if `p = 5`, then `5 ∣ U` and `5 ∣ V`, so `25 ∣ U*V = 5*B^4`.
  -- Cancelling one factor `5` gives `5 ∣ B^4`, hence `5 ∣ B`, contradicting `p ∤ B`.
  have h5U : (5 : ℤ) ∣ U r B s := by
    simpa [hp_eq5] using hpU
  have h5V : (5 : ℤ) ∣ V r B s := by
    simpa [hp_eq5] using hpV
  have h25UV : (25 : ℤ) ∣ U r B s * V r B s := by
    rcases h5U with ⟨u, hu⟩
    rcases h5V with ⟨v, hv⟩
    refine ⟨u * v, ?_⟩
    rw [hu, hv]
    ring
  have h25rhs : (25 : ℤ) ∣ 5 * B ^ 4 := by
    rwa [hUV] at h25UV
  have h5B4 : (5 : ℤ) ∣ B ^ 4 := by
    rcases h25rhs with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0)
    calc
      5 * B ^ 4 = 25 * k := hk
      _ = 5 * (5 * k) := by ring
  have h5B : (5 : ℤ) ∣ B :=
    Int.Prime.dvd_pow' (by norm_num : Nat.Prime 5) h5B4
  exact hp_not_B (by simpa [hp_eq5] using h5B)

/-- The gcd theorem in the natural `Odd` form. -/
theorem quarticPlus_gcd_UV_eq_one
    {r B s : ℤ}
    (hrodd : Odd r)
    (hBodd : Odd B)
    (hcop : Int.gcd r B = 1)
    (hs : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    Int.gcd (U r B s) (V r B s) = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one, Int.isCoprime_iff_nat_coprime]
  by_contra hnot
  rcases Nat.Prime.not_coprime_iff_dvd.mp hnot with ⟨p, hp, hpU_abs, hpV_abs⟩
  have hpU : (p : ℤ) ∣ U r B s := Int.natCast_dvd.mpr hpU_abs
  have hpV : (p : ℤ) ∣ V r B s := Int.natCast_dvd.mpr hpV_abs
  exact quartic_common_prime_UV_false
    (r := r) (B := B) (s := s) hp hpU hpV hrodd hBodd hcop hs

/-- Exact wrapper for hypotheses written as `r % 2 = 1`, `B % 2 = 1`. -/
theorem quarticPlus_gcd_UV_eq_one_of_emod
    {r B s : ℤ}
    (hrodd : r % 2 = 1)
    (hBodd : B % 2 = 1)
    (hcop : Int.gcd r B = 1)
    (hs : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    Int.gcd (2 * r ^ 2 + B ^ 2 - 2 * s)
      (2 * r ^ 2 + B ^ 2 + 2 * s) = 1 := by
  have hrOdd : Odd r := odd_of_emod_two_eq_one hrodd
  have hBOdd : Odd B := odd_of_emod_two_eq_one hBodd
  simpa [U, V] using
    quarticPlus_gcd_UV_eq_one
      (r := r) (B := B) (s := s) hrOdd hBOdd hcop hs

end DM1
```

The main downstream theorem to use with your current hypotheses is:

```lean
DM1.quarticPlus_gcd_UV_eq_one_of_emod
```

If your local context already stores oddness as `Odd r` and `Odd B`, use:

```lean
DM1.quarticPlus_gcd_UV_eq_one
```
