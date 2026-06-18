# ChatGPT Drop File (dm2)

The target is the `d = 10` quartic obstruction:

```lean
theorem quartic_no_sol_d10 (s t : ℤ) (hcop : Int.gcd s 10 = 1) :
    s ^ 4 + 100 * s ^ 2 - 10000 = t ^ 2 → False
```

There is a shorter proof than a large-case squeeze.  The hypothesis `Int.gcd s 10 = 1` excludes even `s`, so `s` is odd.  Since `Int.even_or_odd` gives representatives as `a + a` and `a + a + 1`, the proof below first normalizes these forms to `2 * a` and `2 * a + 1` with `omega`.

In the odd branch, substituting `s = 2*a + 1` gives

```text
s^4 + 100*s^2 - 10000 = 8*(2*a^4 + 4*a^3 + 53*a^2 + 51*a - 1238) + 5.
```

Thus `t^2 ≡ 5 mod 8`, impossible because an even square is `0 mod 4` and an odd square is `1 mod 4`, hence no square is `5 mod 8`.  The Lean proof implements this with the same integer-residue style used in the descent files: split `t` by parity, expand with `nlinarith`, then close with `omega`.

```lean
import Mathlib

/-!
# The `d = 10` quartic obstruction

We prove that `s^4 + 100*s^2 - 10000 = t^2` has no integer solution when
`Int.gcd s 10 = 1`.  Since the gcd hypothesis forces `s` odd, the left hand side
is `5 mod 8`, which is not a square modulo `8`.
-/

private lemma two_dvd_Int_gcd_even_ten (a : ℤ) :
    (2 : ℕ) ∣ Int.gcd (2 * a) 10 := by
  change (2 : ℕ) ∣ Nat.gcd ((2 * a : ℤ).natAbs) ((10 : ℤ).natAbs)
  exact Nat.dvd_gcd
    (by simpa [Int.natAbs_mul] using (Nat.dvd_mul_right 2 a.natAbs))
    (by norm_num)

private lemma square_not_eight_mul_add_five (t K : ℤ)
    (h : t ^ 2 = 8 * K + 5) : False := by
  rcases Int.even_or_odd t with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have : 4 * c ^ 2 = 8 * K + 5 := by nlinarith
    omega
  · have : 4 * c ^ 2 + 4 * c + 1 = 8 * K + 5 := by nlinarith
    omega

theorem quartic_no_sol_d10 (s t : ℤ) (hcop : Int.gcd s 10 = 1) :
    s ^ 4 + 100 * s ^ 2 - 10000 = t ^ 2 → False := by
  intro h
  rcases Int.even_or_odd s with ⟨a, hs⟩ | ⟨a, hs⟩
  · have hs2 : s = 2 * a := by omega
    have h2g : (2 : ℕ) ∣ Int.gcd s 10 := by
      rw [hs2]
      exact two_dvd_Int_gcd_even_ten a
    rw [hcop] at h2g
    norm_num at h2g
  · have hs2 : s = 2 * a + 1 := by omega
    have hmod :
        t ^ 2 = 8 * (2 * a ^ 4 + 4 * a ^ 3 + 53 * a ^ 2 + 51 * a - 1238) + 5 := by
      rw [← h, hs2]
      ring
    exact square_not_eight_mul_add_five t _ hmod
```
