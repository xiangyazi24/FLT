# Q1600 (dm1): factoring the even-`B` case and proving `gcd(u,v)=1`

Yes, the corrected argument is right.

In the even-`B` branch you should **not** factor

```lean
(r - h) * (r + h) = 4 * b ^ 4
```

directly. Since `r` is odd and `h = a ^ 2 - b ^ 2` is odd, both `r-h` and `r+h` are even. Define

```lean
u = (r - h) / 2
v = (r + h) / 2
```

Then

```lean
u * v = b ^ 4
u + v = r
v - u = h
```

The gcd proof is simpler than the modular-inverse route: you do **not** need to use `p ∣ h` to prove `p ∣ b`. If a prime `p` divides both `u` and `v`, then `p ∣ u+v = r`. Also `p ∣ u*v = b^4`, hence `p ∣ b`. Since `b ∣ B₁` and `B = 2*B₁`, this gives `p ∣ B`. Thus `p ∣ gcd(r,B)=1`, contradiction.

So the right Lean lemma is parameterized by the product `u*v=b^4` and the sum `u+v=r`; it does not need the difference `v-u=h` for the gcd part.

## Lean skeleton for the half-factor setup

Use this immediately after proving

```lean
hr_sq : r ^ 2 = h ^ 2 + 4 * b ^ 4
```

where `h = a^2-b^2`.

```lean
import Mathlib

let u : ℤ := (r - h) / 2
let v : ℤ := (r + h) / 2

have h2u_dvd : 2 ∣ r - h := by
  -- from `r % 2 = 1` and `h % 2 = 1`
  exact two_dvd_sub_of_odd_odd hr_odd hh_odd

have h2v_dvd : 2 ∣ r + h := by
  -- from `r % 2 = 1` and `h % 2 = 1`
  exact two_dvd_add_of_odd_odd hr_odd hh_odd

have h2u : 2 * u = r - h := by
  dsimp [u]
  exact (Int.ediv_mul_cancel h2u_dvd).symm

have h2v : 2 * v = r + h := by
  dsimp [v]
  exact (Int.ediv_mul_cancel h2v_dvd).symm

have huv_sum : u + v = r := by
  have h2 : 2 * (u + v) = 2 * r := by
    nlinarith [h2u, h2v]
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2

have huv_diff : v - u = h := by
  have h2 : 2 * (v - u) = 2 * h := by
    nlinarith [h2u, h2v]
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2

have huv_prod : u * v = b ^ 4 := by
  have hprod0 : (r - h) * (r + h) = 4 * b ^ 4 := by
    nlinarith [hr_sq]
  have hprod1 : (2 * u) * (2 * v) = 4 * b ^ 4 := by
    simpa [h2u, h2v] using hprod0
  have hprod2 : 4 * (u * v) = 4 * b ^ 4 := by
    nlinarith [hprod1]
  exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) hprod2
```

The parity facts are only needed to justify the divisions by `2`. Once `u`, `v`, and `huv_prod` are available, the gcd proof does not use parity.

## The gcd lemma

This is the key reusable lemma for the even case. In the symmetric orientation, replace `b` below by the descent variable, i.e. call the lemma with `y := a`.

```lean
import Mathlib

lemma coprime_half_factors_of_fourth
    {r B B₁ a b u v : ℤ}
    (hu_pos : 0 < u)
    (hv_pos : 0 < v)
    (hB_eq : B = 2 * B₁)
    (hB₁_eq : B₁ = a * b)
    (hcop : Int.gcd r B = 1)
    (hsum : u + v = r)
    (hprod : u * v = b ^ 4) :
    Int.gcd u v = 1 := by
  by_contra hbad

  have hgpos : 0 < Int.gcd u v := by
    exact Int.gcd_pos_of_pos_left v hu_pos

  have hg_gt_one : 1 < Int.gcd u v := by
    omega

  -- Depending on your Mathlib snapshot, this line may be either
  --   Nat.exists_prime_and_dvd (ne_of_gt hg_gt_one)
  -- or
  --   Nat.exists_prime_and_dvd hg_gt_one
  obtain ⟨p, hp_prime, hp_dvd_g⟩ :=
    Nat.exists_prime_and_dvd (ne_of_gt hg_gt_one)

  have hp_dvd_g_int : (p : ℤ) ∣ (Int.gcd u v : ℤ) := by
    exact_mod_cast hp_dvd_g

  have hpu : (p : ℤ) ∣ u := by
    exact dvd_trans hp_dvd_g_int (Int.gcd_dvd_left u v)

  have hpv : (p : ℤ) ∣ v := by
    exact dvd_trans hp_dvd_g_int (Int.gcd_dvd_right u v)

  -- Prime p divides u+v = r.
  have hp_r : (p : ℤ) ∣ r := by
    have hp_sum : (p : ℤ) ∣ u + v := dvd_add hpu hpv
    simpa [hsum] using hp_sum

  -- Prime p divides u*v = b^4, hence p divides b.
  have hp_b4 : (p : ℤ) ∣ b ^ 4 := by
    have hp_uv : (p : ℤ) ∣ u * v := dvd_mul_of_dvd_left hpu v
    simpa [hprod] using hp_uv

  have hpZ_prime : Prime (p : ℤ) := by
    -- Use the same Nat-prime-to-Int-prime bridge already used in your file
    -- if `exact_mod_cast hp_prime` is not accepted by your Mathlib snapshot.
    exact_mod_cast hp_prime

  have hp_b : (p : ℤ) ∣ b := by
    exact hpZ_prime.dvd_of_dvd_pow hp_b4

  -- Since B₁ = a*b, p divides B₁; since B = 2*B₁, p divides B.
  have hp_B₁ : (p : ℤ) ∣ B₁ := by
    rw [hB₁_eq]
    exact dvd_mul_of_dvd_right hp_b a

  have hp_B : (p : ℤ) ∣ B := by
    rw [hB_eq]
    exact dvd_mul_of_dvd_right hp_B₁ 2

  have hp_gcd : (p : ℤ) ∣ (Int.gcd r B : ℤ) := by
    exact Int.dvd_gcd hp_r hp_B

  have hp_one : (p : ℤ) ∣ (1 : ℤ) := by
    simpa [hcop] using hp_gcd

  have hp_one_nat : p ∣ (1 : ℕ) := by
    exact_mod_cast hp_one

  exact hp_prime.not_dvd_one hp_one_nat
```

If `Nat.exists_prime_and_dvd` in your Mathlib has a different signature, replace only that `obtain` line with the one from your existing `UV_coprime` proof. The divisibility spine after `hpu` and `hpv` is the important part and should be stable.

## Positivity of `u` and `v`

The gcd lemma above assumes `0 < u` and `0 < v` only to get `1 < Int.gcd u v` under `by_contra`. Prove positivity from

```lean
hr_sq : r ^ 2 = h ^ 2 + 4 * b ^ 4
hb : 0 < b
hr : 0 < r
```

Mathematically, `4*b^4 > 0`, so `h^2 < r^2`, hence `-r < h < r`, hence `r-h > 0` and `r+h > 0`; after division by positive `2`, both half-factors are positive. In Lean, package this once:

```lean
have hu_pos : 0 < u := by
  exact half_factor_left_pos hr hb hr_sq h2u

have hv_pos : 0 < v := by
  exact half_factor_right_pos hr hb hr_sq h2v
```

Those two helpers are pure inequality lemmas and independent of the quartic descent.

## How it plugs into the even descent

After the gcd lemma:

```lean
have huv_cop : Int.gcd u v = 1 := by
  exact coprime_half_factors_of_fourth
    hu_pos hv_pos hB_eq_two hB₁_eq hcop huv_sum huv_prod
```

then apply the same fourth-power product split as in the odd case:

```lean
obtain ⟨α, β, hαpos, hβpos, hu_eq, hv_eq, hb_eq⟩ :=
  coprime_product_eq_fourth_split hu_pos hv_pos huv_cop huv_prod hb
```

where the intended outputs are

```lean
hu_eq : u = α ^ 4
hv_eq : v = β ^ 4
hb_eq : b = α * β
```

Then

```lean
h = v - u = β ^ 4 - α ^ 4
h = a ^ 2 - b ^ 2
b = α * β
```

implies

```lean
a ^ 2 = β ^ 4 + β ^ 2 * α ^ 2 - α ^ 4
```

and the new solution is again

```lean
⟨β, α, a⟩
```

for the main orientation. For the symmetric orientation, swap `a` and `b`, so the descent variable is `a` and the new solution is `⟨β, α, b⟩`.

## Bottom line

The proof of `gcd(u,v)=1` is correct, and the clean version is:

```text
p | u and p | v
⇒ p | u+v = r
⇒ p | u*v = b⁴
⇒ p | b
⇒ p | B₁
⇒ p | B
⇒ p | gcd(r,B)=1, contradiction.
```

No modular inversion, no use of `p ∤ a`, and no need to reason from `p | h = a²-b²`.
