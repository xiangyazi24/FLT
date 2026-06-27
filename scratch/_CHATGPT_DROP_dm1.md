# Q1450 (dm1/dm4): coprime factorization of `5 * B^4`

I would **not** look for or rely on an `Int.fourth_of_gcd_eq_one` theorem here.  The clean route is:

1. move the factorization lemma to `ℕ` using positivity of `U,V,B`;
2. split the single extra prime `5` first;
3. after cancellation, use a generic coprime-product-is-fourth-power lemma;
4. cast the result back to `ℤ`.

The exact mathematical split is the one you sketched, with one correction about orientation:

```text
if 5 ∣ U, then U = 5*a^4 and V = b^4;
if 5 ∣ V, then U = a^4 and V = 5*b^4.
```

So the target theorem should be proved from a reusable `Nat` helper.

## Recommended generic helper

Do this once over `ℕ`:

```lean
import Mathlib

namespace DM1

/--
Generic helper: coprime positive factors of a fourth power are fourth powers.

This is the lemma to prove by either:
* iterating your existing square-product lemma twice, or
* using `Nat.factorization`.
-/
lemma coprime_mul_eq_fourth_nat {x y z : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hcop : x.Coprime y)
    (hxy : x * y = z ^ 4) :
    ∃ a b : ℕ,
      0 < a ∧ 0 < b ∧ a.Coprime b ∧ a * b = z ∧
        x = a ^ 4 ∧ y = b ^ 4 := by
  -- Proof route A: iterate square splitting.
  --
  -- First use the square lemma on
  --   x*y = (z^2)^2
  -- to get x = x1^2, y = y1^2, x1*y1 = z^2.
  -- Then prove x1.Coprime y1 from x.Coprime y using:
  --   Nat.coprime_pow_left_iff
  --   Nat.coprime_pow_right_iff
  -- Finally apply the same square lemma to x1*y1 = z^2.
  --
  -- Proof route B: use Nat.factorization directly.
  -- For every prime p, coprimality says the p-adic exponent lives entirely
  -- in x or entirely in y.  Since x*y = z^4, that exponent is divisible by 4.
  -- Then reconstruct a and b from factorization exponents divided by 4.
  sorry
```

The important point in the iterative proof is the middle coprimality step.  If the first square split gives

```lean
x = x1 ^ 2
 y = y1 ^ 2
```

then from `hcop : x.Coprime y` you get `x1.Coprime y1` by stripping powers:

```lean
have hcop_sq : (x1 ^ 2).Coprime (y1 ^ 2) := by
  simpa [hx1, hy1] using hcop
have hcop_x1_y1_sq : x1.Coprime (y1 ^ 2) :=
  (Nat.coprime_pow_left_iff (by decide : 0 < 2) x1 (y1 ^ 2)).mp hcop_sq
have hcop_x1_y1 : x1.Coprime y1 :=
  (Nat.coprime_pow_right_iff (by decide : 0 < 2) x1 y1).mp hcop_x1_y1_sq
```

That is the piece that makes “iterate `sq_of_gcd_eq_one` twice” legitimate.

## The `5 * B^4` factorization lemma over `ℕ`

After the helper above, the special factorization theorem is straightforward.

```lean
/-- Positive coprime factorization of `5 * B^4`. -/
theorem coprime_factorization_five_fourth_nat {U V B : ℕ}
    (hUpos : 0 < U) (hVpos : 0 < V) (hBpos : 0 < B)
    (hcop : U.Coprime V)
    (hUV : U * V = 5 * B ^ 4) :
    ∃ a b : ℕ,
      0 < a ∧ 0 < b ∧ a.Coprime b ∧ a * b = B ∧
        ((U = a ^ 4 ∧ V = 5 * b ^ 4) ∨
         (U = 5 * a ^ 4 ∧ V = b ^ 4)) := by
  classical
  have h5prime : Nat.Prime 5 := by norm_num
  have h5prod : 5 ∣ U * V := by
    rw [hUV]
    exact dvd_mul_right 5 (B ^ 4)
  rcases h5prime.dvd_mul.mp h5prod with h5U | h5V
  · -- Branch `5 ∣ U`: write U = 5*U0 and cancel the 5.
    let U0 : ℕ := U / 5
    have hUeq : U = 5 * U0 := by
      -- `Nat.div_mul_cancel` / `Nat.mul_div_right'` depending on local API.
      exact (Nat.div_mul_cancel h5U).symm
    have hU0pos : 0 < U0 := by
      -- from hUpos and hUeq
      omega
    have hU0dvd : U0 ∣ U := by
      refine ⟨5, ?_⟩
      rw [mul_comm, hUeq]
    have hcop0 : U0.Coprime V := hcop.of_dvd_left hU0dvd
    have hcancel : U0 * V = B ^ 4 := by
      -- Substitute U = 5*U0 in hUV and cancel the positive factor 5.
      -- `nlinarith` after `rw [hUeq] at hUV` often works; otherwise use
      -- `Nat.mul_left_cancel` on `5 * (U0*V) = 5 * B^4`.
      rw [hUeq] at hUV
      nlinarith
    rcases coprime_mul_eq_fourth_nat hU0pos hVpos hBpos hcop0 hcancel with
      ⟨a, b, ha, hb, habcop, hab, hU0fourth, hVfourth⟩
    refine ⟨a, b, ha, hb, habcop, hab, Or.inr ?_⟩
    constructor
    · rw [hUeq, hU0fourth]
    · exact hVfourth
  · -- Branch `5 ∣ V`: symmetric.
    let V0 : ℕ := V / 5
    have hVeq : V = 5 * V0 := by
      exact (Nat.div_mul_cancel h5V).symm
    have hV0pos : 0 < V0 := by
      omega
    have hV0dvd : V0 ∣ V := by
      refine ⟨5, ?_⟩
      rw [mul_comm, hVeq]
    have hcop0 : U.Coprime V0 := hcop.of_dvd_right hV0dvd
    have hcancel : U * V0 = B ^ 4 := by
      rw [hVeq] at hUV
      nlinarith
    rcases coprime_mul_eq_fourth_nat hUpos hV0pos hBpos hcop0 hcancel with
      ⟨a, b, ha, hb, habcop, hab, hUfourth, hV0fourth⟩
    refine ⟨a, b, ha, hb, habcop, hab, Or.inl ?_⟩
    constructor
    · exact hUfourth
    · rw [hVeq, hV0fourth]

end DM1
```

You may need to adjust the exact cancellation line depending on the local `Nat` API: the stable mathematical move is to rewrite `U = 5*U0` or `V = 5*V0`, reassociate to

```lean
5 * (U0 * V) = 5 * B ^ 4
```

or

```lean
5 * (U * V0) = 5 * B ^ 4
```

then apply `Nat.mul_left_cancel`.

## Int wrapper shape

For the quartic descent theorem itself, keep the public theorem over `ℤ`, but prove it by converting to naturals:

```lean
theorem coprime_factorization_five_fourth_int {U V B : ℤ}
    (hUpos : 0 < U) (hVpos : 0 < V) (hBpos : 0 < B)
    (hcop : Int.gcd U V = 1)
    (hUV : U * V = 5 * B ^ 4) :
    ∃ a b : ℤ,
      0 < a ∧ 0 < b ∧ Int.gcd a b = 1 ∧ a * b = B ∧
        ((U = a ^ 4 ∧ V = 5 * b ^ 4) ∨
         (U = 5 * a ^ 4 ∧ V = b ^ 4)) := by
  -- Set u := U.natAbs, v := V.natAbs, b := B.natAbs.
  -- Positivity makes `U = (u : ℤ)`, etc.
  -- Convert hUV and hcop to:
  --   u * v = 5 * b ^ 4
  --   u.Coprime v
  -- Apply `coprime_factorization_five_fourth_nat`.
  -- Cast the resulting natural a,b back to integers.
  sorry
```

So the answer to your API question is: do **not** try to find a fourth-power version.  Either iterate the square-product lemma twice after splitting off the `5`, or prove the generic `Nat` helper directly with `Nat.factorization`.  The special `5*B^4` statement should then be a short branch on `5 ∣ U ∨ 5 ∣ V`.