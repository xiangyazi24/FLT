# Q2451 coprime cofactor gcd lemma Lean route

## Verdict

The stated lemma is true. No corrected hypothesis is needed for the displayed statement.

The positivity assumptions

```lean
(hapos : 0 < a) (hdpos : 0 < d)
```

are convenient for a Nat-cast bridge, but they are not mathematically essential because only `a^2` and `d^2` occur. A stronger Int statement should also be true with only

```lean
(had : IsCoprime a d) (hdodd : Odd d)
```

The oddness hypothesis is genuinely needed. If it is removed, take `a = 1`, `d = 2`: then `IsCoprime (1 : ℤ) 2`, but

```text
4*1^2 + 2^2 = 8,
16*1^2 + 2^2 = 20,
gcd(8,20)=4.
```

The `had` hypothesis is also doing real work for the mod-3 exclusion.

## Recommended Lean route

Do the arithmetic over `ℕ`, then cast back to `ℤ` using positivity. The Nat core is cleaner because prime-divisor APIs are strong there.

Target Nat core:

```lean
import Mathlib

/-- Nat core for the EulerAux cofactor gcd. -/
theorem nat_coprime_four_sq_add_sq_sixteen_sq_add_sq
    {a d : ℕ}
    (had : Nat.Coprime a d)
    (hdodd : Odd d) :
    Nat.Coprime (4*a^2 + d^2) (16*a^2 + d^2) := by
  -- prove by `Nat.coprime_of_dvd'`:
  -- for every prime `p` dividing both, show `p ∣ 1` by contradiction.
  sorry
```

Then the requested Int theorem is a short bridge:

```lean
theorem coprime_four_sq_add_d_sq_sixteen_sq_add_d_sq
    {a d : ℤ}
    (hapos : 0 < a)
    (hdpos : 0 < d)
    (had : IsCoprime a d)
    (hdodd : Odd d) :
    IsCoprime (4*a^2 + d^2) (16*a^2 + d^2) := by
  let A : ℕ := a.natAbs
  let D : ℕ := d.natAbs
  have hA : (A : ℤ) = a := by
    simpa [A] using Int.natAbs_of_nonneg hapos.le
  have hD : (D : ℤ) = d := by
    simpa [D] using Int.natAbs_of_nonneg hdpos.le
  have hadNat : Nat.Coprime A D := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hg : Int.gcd a d = 1 := Int.isCoprime_iff_gcd_eq_one.mp had
    simpa [A, D, Int.gcd_def] using hg
  have hDodd : Odd D := by
    simpa [A, D, Int.natAbs_odd] using hdodd
  have hNat := nat_coprime_four_sq_add_sq_sixteen_sq_add_sq hadNat hDodd
  have hInt : IsCoprime ((4*A^2 + D^2 : ℕ) : ℤ) ((16*A^2 + D^2 : ℕ) : ℤ) :=
    Nat.Coprime.isCoprime hNat
  have hx : ((4*A^2 + D^2 : ℕ) : ℤ) = 4*a^2 + d^2 := by
    norm_num [hA, hD]
  have hy : ((16*A^2 + D^2 : ℕ) : ℤ) = 16*a^2 + d^2 := by
    norm_num [hA, hD]
  simpa [hx, hy] using hInt
```

If the final `norm_num [hA, hD]` does not unfold the Nat casts in your Mathlib snapshot, replace each with:

```lean
  norm_cast
  ring_nf
  all_goals simp [hA, hD]
```

or prove the two cast equalities by `norm_num [A, D, hA, hD]`.

## Theorem DAG for the Nat core

Use this DAG.

```lean
import Mathlib

lemma odd_four_sq_add_sq
    {a d : ℕ} (hdodd : Odd d) :
    Odd (4*a^2 + d^2) := by
  have h4 : Even (4 * a^2) := by
    refine ⟨2 * a^2, ?_⟩
    ring
  have hd2 : Odd (d^2) := hdodd.pow
  exact h4.add_odd hd2

lemma three_dvd_of_three_dvd_four_sq_add_sq
    {a d : ℕ}
    (h : 3 ∣ 4*a^2 + d^2) :
    3 ∣ a ∧ 3 ∣ d := by
  let A : ZMod 3 := a
  let D : ZMod 3 := d
  have hsum : A^2 + D^2 = 0 := by
    have hcast : ((4*a^2 + d^2 : ℕ) : ZMod 3) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod 3) 3 (4*a^2 + d^2)).2 h
    -- In `ZMod 3`, `4 = 1`; cast normalization usually succeeds with this:
    norm_num [A, D] at hcast ⊢
  have hAD : A = 0 ∧ D = 0 := by
    fin_cases A <;> fin_cases D <;> norm_num at hsum ⊢
  constructor
  · exact (CharP.cast_eq_zero_iff (ZMod 3) 3 a).1 (by simpa [A] using hAD.1)
  · exact (CharP.cast_eq_zero_iff (ZMod 3) 3 d).1 (by simpa [D] using hAD.2)

lemma not_three_dvd_four_sq_add_sq_of_coprime
    {a d : ℕ}
    (had : Nat.Coprime a d) :
    ¬ 3 ∣ 4*a^2 + d^2 := by
  intro h
  rcases three_dvd_of_three_dvd_four_sq_add_sq h with ⟨h3a, h3d⟩
  have h31 : (3 : ℕ) = 1 := Nat.eq_one_of_dvd_coprimes had h3a h3d
  norm_num at h31

lemma prime_not_dvd_a_of_dvd_four_sq_add_sq
    {p a d : ℕ}
    (hp : p.Prime)
    (had : Nat.Coprime a d)
    (hpX : p ∣ 4*a^2 + d^2) :
    ¬ p ∣ a := by
  intro hpa
  have hp4a2 : p ∣ 4*a^2 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpa 2) 4
  have hpdsq : p ∣ d^2 := by
    have hsub := Nat.dvd_sub hpX hp4a2 (by nlinarith)
    convert hsub using 1
    nlinarith
  have hpd : p ∣ d := hp.dvd_of_dvd_pow hpdsq
  have hp1 : p = 1 := Nat.eq_one_of_dvd_coprimes had hpa hpd
  exact hp.one_lt.ne' hp1

lemma prime_dvd_twelve_of_dvd_both_four_sixteen
    {p a d : ℕ}
    (hp : p.Prime)
    (had : Nat.Coprime a d)
    (hpX : p ∣ 4*a^2 + d^2)
    (hpY : p ∣ 16*a^2 + d^2) :
    p ∣ 12 := by
  have hp_not_a : ¬ p ∣ a :=
    prime_not_dvd_a_of_dvd_four_sq_add_sq hp had hpX
  have hp12a2 : p ∣ 12*a^2 := by
    have hsub := Nat.dvd_sub hpY hpX (by nlinarith)
    convert hsub using 1
    nlinarith
  rcases hp.dvd_mul.mp hp12a2 with hp12 | hpa2
  · exact hp12
  · exact False.elim (hp_not_a (hp.dvd_of_dvd_pow hpa2))

lemma prime_eq_two_or_three_of_dvd_twelve
    {p : ℕ}
    (hp : p.Prime)
    (hp12 : p ∣ 12) :
    p = 2 ∨ p = 3 := by
  have hp_le : p ≤ 12 := Nat.le_of_dvd (by decide : 0 < 12) hp12
  interval_cases p <;> norm_num at hp hp12 ⊢
```

With those in place, the Nat core is direct:

```lean
theorem nat_coprime_four_sq_add_sq_sixteen_sq_add_sq
    {a d : ℕ}
    (had : Nat.Coprime a d)
    (hdodd : Odd d) :
    Nat.Coprime (4*a^2 + d^2) (16*a^2 + d^2) := by
  refine Nat.coprime_of_dvd' ?_
  intro p hp hpX hpY
  have hp12 : p ∣ 12 :=
    prime_dvd_twelve_of_dvd_both_four_sixteen hp had hpX hpY
  rcases prime_eq_two_or_three_of_dvd_twelve hp hp12 with rfl | rfl
  · exact False.elim ((odd_four_sq_add_sq hdodd).not_two_dvd_nat hpX)
  · exact False.elim ((not_three_dvd_four_sq_add_sq_of_coprime had) hpX)
```

This avoids denominator clearing and avoids any AP theorem.

## Alternative `Int.gcd = 1` formulation

If you prefer to keep the main theorem in `ℤ`, use this equivalent target:

```lean
theorem coprime_four_sq_add_d_sq_sixteen_sq_add_d_sq_gcd
    {a d : ℤ}
    (hapos : 0 < a)
    (hdpos : 0 < d)
    (had : IsCoprime a d)
    (hdodd : Odd d) :
    Int.gcd (4*a^2 + d^2) (16*a^2 + d^2) = 1 := by
  exact Int.isCoprime_iff_gcd_eq_one.mp
    (coprime_four_sq_add_d_sq_sixteen_sq_add_d_sq hapos hdpos had hdodd)
```

And conversely:

```lean
  exact Int.isCoprime_iff_gcd_eq_one.mpr h_gcd
```

## APIs to grep/check

```lean
#check Nat.coprime_of_dvd'
#check Nat.Prime.not_coprime_iff_dvd
#check Nat.eq_one_of_dvd_coprimes
#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_of_dvd_pow
#check Nat.dvd_sub
#check Nat.le_of_dvd
#check Nat.dvd_iff_mod_eq_zero
#check Odd.pow
#check Even.add_odd
#check Odd.not_two_dvd_nat
#check CharP.cast_eq_zero_iff
#check ZMod.val_natCast
#check Int.isCoprime_iff_gcd_eq_one
#check Nat.isCoprime_iff_coprime
#check Nat.Coprime.isCoprime
#check Int.gcd_def
#check Int.natAbs_odd
```

Relevant source locations in current Mathlib:

```text
Mathlib/RingTheory/Coprime/Basic.lean      -- `IsCoprime`, `IsCoprime.dvd_of_dvd_mul_*`, symmetry, products
Mathlib/RingTheory/Coprime/Lemmas.lean     -- `Int.isCoprime_iff_gcd_eq_one`, `Nat.isCoprime_iff_coprime`, `IsCoprime.pow_*`
Mathlib/Data/Nat/GCD/Basic.lean            -- `Nat.eq_one_of_dvd_coprimes`, `Nat.Coprime.dvd_mul_*`
Mathlib/Data/Nat/Prime/Basic.lean          -- `Nat.coprime_of_dvd'`, `Prime.dvd_of_dvd_pow`, prime/coprime APIs
Mathlib/Algebra/Ring/Parity.lean           -- `Odd.pow`, `Even.add_odd`, Nat odd lemmas
Mathlib/Algebra/Ring/Int/Parity.lean       -- `Int.natAbs_odd`, `Int.odd_iff`
Mathlib/Data/ZMod/Basic.lean               -- `ZMod`, `CharP` instance, finite cases support
Mathlib/Algebra/CharP/Basic.lean           -- `CharP.cast_eq_zero_iff`
```

## Notes on likely minor elaboration fixes

1. If `Nat.dvd_sub` argument order differs in the local snapshot, check:

```lean
#check Nat.dvd_sub
```

The intended use is: from `p ∣ Y`, `p ∣ X`, and `X ≤ Y`, get `p ∣ Y - X`.

2. If the `ZMod 3` cast normalization line in `three_dvd_of_three_dvd_four_sq_add_sq` does not close with

```lean
norm_num [A, D] at hcast ⊢
```

replace that proof with a pure `Nat.mod` proof using:

```lean
Nat.dvd_iff_mod_eq_zero
Nat.mod_lt
interval_cases a % 3
interval_cases d % 3
```

The finite check is only the table

```text
x^2 mod 3 ∈ {0,1};
4*x^2 + y^2 ≡ x^2 + y^2;
only x ≡ y ≡ 0 gives 0 mod 3.
```

3. If the final Int bridge has trouble with `Odd D`, this is the intended one-liner:

```lean
have hDodd : Odd D := by
  simpa [D, Int.natAbs_odd] using hdodd
```

`Int.natAbs_odd` has shape `Odd n.natAbs ↔ Odd n`.
