# Q1739 (dm2/dm4): `coprime_uv` for the halved odd/odd case

## Verdict

Do **not** try to reuse `coprime_rh` directly.  The obstruction is real: that lemma is for the unhalved factor pair and assumes the parity package in which the auxiliary `h` is even.  In the even-`B` branch here, the natural `h = a^2 - b^2` is odd, so the right pair is

```lean
u = (r - h) / 2
v = (r + h) / 2
```

and the proof should be based on

```lean
u + v = r
u * v = b ^ 4
```

The clean lemma is therefore a new `coprime_uv_of_prod`: if you already have the product identity, it proves the gcd immediately.  I also include a wrapper `coprime_uv` for the common local identity

```lean
r ^ 2 = h ^ 2 + 4 * b ^ 4
```

which derives `u * v = b ^ 4` from oddness of `r` and `h`.

## Concrete Lean code

```lean
import Mathlib

namespace FLT.DM4

/--
A tiny coercion helper: if a natural number, viewed as an integer, divides `1`,
then it is `1`.
-/
private lemma nat_eq_one_of_coe_int_dvd_one {d : ℕ}
    (hd : (d : ℤ) ∣ (1 : ℤ)) : d = 1 := by
  rcases hd with ⟨k, hk⟩
  have hd_nonneg : 0 ≤ (d : ℤ) := by
    exact_mod_cast Nat.zero_le d
  have hd_ne_zero : (d : ℤ) ≠ 0 := by
    intro hzero
    rw [hzero] at hk
    norm_num at hk
  have hd_pos : 0 < (d : ℤ) :=
    lt_of_le_of_ne hd_nonneg (Ne.symm hd_ne_zero)
  have hk_pos : 0 < k := by
    nlinarith [hk, hd_pos]
  have hk_ge_one : 1 ≤ k := by omega
  have hd_le_one : (d : ℤ) ≤ 1 := by
    nlinarith [hk, hd_pos, hk_ge_one]
  have hd_ge_one : 1 ≤ (d : ℤ) := by omega
  have hd_eq : (d : ℤ) = 1 := by omega
  exact_mod_cast hd_eq

/--
If `a` is coprime to `b`, then it is coprime to every power of `b`.
This is just the `Nat.Coprime.pow_right` API, transported through `Int.gcd`.
-/
private lemma int_gcd_pow_right_eq_one {a b : ℤ}
    (hcop : Int.gcd a b = 1) (n : ℕ) :
    Int.gcd a (b ^ n) = 1 := by
  have hcopN : Nat.Coprime a.natAbs b.natAbs := by
    simpa [Int.gcd, Nat.Coprime] using hcop
  have hpowN : Nat.Coprime a.natAbs ((b ^ n).natAbs) := by
    simpa [Int.natAbs_pow] using hcopN.pow_right n
  simpa [Int.gcd, Nat.Coprime] using hpowN

/--
Useful when the branch gives `b ∣ B₁` and `gcd r B₁ = 1`.
-/
private lemma int_gcd_eq_one_of_right_dvd {r b B : ℤ}
    (hcop : Int.gcd r B = 1) (hbB : b ∣ B) :
    Int.gcd r b = 1 := by
  let d : ℕ := Int.gcd r b
  have hd_r : (d : ℤ) ∣ r := by
    dsimp [d]
    exact Int.gcd_dvd_left r b
  have hd_b : (d : ℤ) ∣ b := by
    dsimp [d]
    exact Int.gcd_dvd_right r b
  have hd_B : (d : ℤ) ∣ B := dvd_trans hd_b hbB
  have hd_gcd : (d : ℤ) ∣ (Int.gcd r B : ℤ) :=
    Int.dvd_coe_gcd hd_r hd_B
  rw [hcop] at hd_gcd
  change d = 1
  exact nat_eq_one_of_coe_int_dvd_one hd_gcd

/--
Core halved-pair lemma.

Use this version if the even branch has already established

`((r - h) / 2) * ((r + h) / 2) = b ^ 4`.

The proof is exactly the prime-divisor argument in gcd form:
if `d = gcd u v`, then `d ∣ u + v = r` and `d ∣ u*v = b^4`.
Since `gcd r b = 1`, also `gcd r (b^4) = 1`, hence `d = 1`.
-/
private theorem coprime_uv_of_prod {r h b : ℤ}
    (hr_odd : r % 2 = 1) (hh_odd : h % 2 = 1)
    (hcop : Int.gcd r b = 1)
    (huv : ((r - h) / 2) * ((r + h) / 2) = b ^ 4) :
    Int.gcd ((r - h) / 2) ((r + h) / 2) = 1 := by
  let u : ℤ := (r - h) / 2
  let v : ℤ := (r + h) / 2

  have hsum : u + v = r := by
    dsimp [u, v]
    omega

  have hprod : u * v = b ^ 4 := by
    simpa [u, v] using huv

  let d : ℕ := Int.gcd u v

  have hd_u : (d : ℤ) ∣ u := by
    dsimp [d]
    exact Int.gcd_dvd_left u v
  have hd_v : (d : ℤ) ∣ v := by
    dsimp [d]
    exact Int.gcd_dvd_right u v

  have hd_r : (d : ℤ) ∣ r := by
    have hdiv : (d : ℤ) ∣ u + v := dvd_add hd_u hd_v
    simpa [hsum] using hdiv

  have hd_b4 : (d : ℤ) ∣ b ^ 4 := by
    have hdiv : (d : ℤ) ∣ u * v := dvd_mul_of_dvd_left hd_u v
    simpa [hprod] using hdiv

  have hcop_pow : Int.gcd r (b ^ 4) = 1 :=
    int_gcd_pow_right_eq_one (a := r) (b := b) hcop 4

  have hd_gcd : (d : ℤ) ∣ (Int.gcd r (b ^ 4) : ℤ) :=
    Int.dvd_coe_gcd hd_r hd_b4
  rw [hcop_pow] at hd_gcd

  change d = 1
  exact nat_eq_one_of_coe_int_dvd_one hd_gcd

/--
Wrapper form when the local identity is

`r^2 = h^2 + 4*b^4`.

Because `r` and `h` are both odd, `r-h` and `r+h` are both divisible by `2`,
so the product of the halves is exactly `b^4`.
-/
private theorem coprime_uv {r h b : ℤ}
    (hr_odd : r % 2 = 1) (hh_odd : h % 2 = 1)
    (hcop : Int.gcd r b = 1)
    (heq : r ^ 2 = h ^ 2 + 4 * b ^ 4) :
    Int.gcd ((r - h) / 2) ((r + h) / 2) = 1 := by
  have hminus : r - h = 2 * ((r - h) / 2) := by
    omega
  have hplus : r + h = 2 * ((r + h) / 2) := by
    omega

  have huv : ((r - h) / 2) * ((r + h) / 2) = b ^ 4 := by
    have hdiff : (r - h) * (r + h) = 4 * b ^ 4 := by
      nlinarith [heq]
    nlinarith [hminus, hplus, hdiff]

  exact coprime_uv_of_prod hr_odd hh_odd hcop huv

end FLT.DM4
```

## How I would use it in the even branch

If the local branch has only `gcd(r, B₁) = 1` and `b ∣ B₁`, first derive `gcd(r,b)=1`:

```lean
have hcop_rb : Int.gcd r b = 1 :=
  int_gcd_eq_one_of_right_dvd (r := r) (b := b) (B := B₁) hcop_rB₁ hb_dvd_B₁
```

Then call the product-form lemma if you already have `huv`:

```lean
have huv_cop : Int.gcd ((r - h) / 2) ((r + h) / 2) = 1 :=
  coprime_uv_of_prod
    (r := r) (h := h) (b := b)
    hr_odd hh_odd hcop_rb huv
```

or call the wrapper if your available equation is the square identity:

```lean
have huv_cop : Int.gcd ((r - h) / 2) ((r + h) / 2) = 1 :=
  coprime_uv
    (r := r) (h := h) (b := b)
    hr_odd hh_odd hcop_rb heq
```

The key point is that this avoids the bad parity mismatch with `coprime_rh`; the proof never needs `h` to be even.
