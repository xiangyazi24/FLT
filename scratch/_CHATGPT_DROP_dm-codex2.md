# Q2561 `three_coprime_centerX` for `EulerSquarePair`

Target in `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`:

```lean
theorem three_coprime_centerX (E : EulerSquarePair) :
    IsCoprime (3 : ℤ) E.centerX
```

where `E.centerX = E.B * E.C`.  The clean local decomposition is:

```lean
theorem not_three_dvd_B (E : EulerSquarePair) : ¬ (3 : ℤ) ∣ E.B
theorem not_three_dvd_C (E : EulerSquarePair) : ¬ (3 : ℤ) ∣ E.C

theorem three_coprime_B (E : EulerSquarePair) : IsCoprime (3 : ℤ) E.B
theorem three_coprime_C (E : EulerSquarePair) : IsCoprime (3 : ℤ) E.C

theorem three_coprime_centerX (E : EulerSquarePair) :
    IsCoprime (3 : ℤ) E.centerX
```

The only API-sensitive bridge is the standard prime bridge

```lean
¬ (3 : ℤ) ∣ x  ⟹  IsCoprime (3 : ℤ) x.
```

Everything else is a small `ZMod 3` computation.

## 0. APIs to check

The `ZMod` APIs below are current Mathlib names:

```lean
#check ZMod.intCast_zmod_eq_zero_iff_dvd
-- theorem ZMod.intCast_zmod_eq_zero_iff_dvd (a : ℤ) (b : ℕ) :
--   (a : ZMod b) = 0 ↔ (b : ℤ) ∣ a

#check ZMod.isUnit_iff_coprime
#check ZMod.coprime_mod_iff_coprime
#check ZMod.isUnit_prime_iff_not_dvd
#check ZMod.isUnit_prime_of_not_dvd
```

For the final `IsCoprime` bridge over `ℤ`, check these locally:

```lean
#check Int.prime_three
#check Nat.prime_three
#check Prime.isCoprime_iff_not_dvd
#check Prime.coprime_iff_not_dvd
#check Irreducible.isCoprime_iff_not_dvd
#check Int.isUnit_iff
```

In many Mathlib snapshots, the bridge can be implemented as one of:

```lean
-- likely shape 1
theorem isCoprime_three_int_of_not_dvd {x : ℤ}
    (hx : ¬ (3 : ℤ) ∣ x) : IsCoprime (3 : ℤ) x := by
  exact (show Prime (3 : ℤ) by norm_num).isCoprime_iff_not_dvd.mpr hx

-- likely shape 2, if the lemma is named without the `is` prefix
theorem isCoprime_three_int_of_not_dvd {x : ℤ}
    (hx : ¬ (3 : ℤ) ∣ x) : IsCoprime (3 : ℤ) x := by
  exact (show Prime (3 : ℤ) by norm_num).coprime_iff_not_dvd.mpr hx
```

Do not paste both.  Use `#check` to select the available method name.  If neither name exists, keep the theorem statement and prove it from the divisor criterion for `IsCoprime` plus `Prime`/`Irreducible` divisibility of `3`.

## 1. Local `ZMod 3` square fact

This is the finite-field fact needed twice.  It avoids developing a general theorem about quadratic residues.

```lean
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
```

```lean
namespace EulerSquarePair

private theorem zmod3_sq_add_sq_eq_zero
    {x y : ZMod 3} (h : x ^ 2 + y ^ 2 = 0) :
    x = 0 ∧ y = 0 := by
  revert h
  fin_cases x <;> fin_cases y <;> decide

end EulerSquarePair
```

If `decide` does not reduce the finite cases in your local snapshot, replace the last line by:

```lean
  fin_cases x <;> fin_cases y <;> native_decide
```

or by:

```lean
  fin_cases x <;> fin_cases y <;> norm_num
```

The theorem statement is the stable part.

## 2. Tiny contradiction helper for `E.hADcop`

This is only used after deriving `3 ∣ A` and `3 ∣ D`.

```lean
namespace EulerSquarePair

private theorem not_isUnit_three_int : ¬ IsUnit (3 : ℤ) := by
  norm_num [Int.isUnit_iff]

end EulerSquarePair
```

If `Int.isUnit_iff` has moved in your snapshot, run:

```lean
#check Int.isUnit_iff
#check isUnit_iff_exists_inv
```

A fallback is to let `norm_num` try it without the rewrite:

```lean
private theorem not_isUnit_three_int : ¬ IsUnit (3 : ℤ) := by
  norm_num
```

## 3. Prove `3 ∤ B`

The robust proof is:

1. Assume `3 ∣ B`.
2. Cast `E.hB` to `ZMod 3`; since `16 = 1` in `ZMod 3`, get
   `(B : ZMod 3)^2 = (A : ZMod 3)^2 + (D : ZMod 3)^2`.
3. `3 ∣ B` gives `(B : ZMod 3) = 0` via `ZMod.intCast_zmod_eq_zero_iff_dvd`.
4. The square fact gives `(A : ZMod 3) = 0` and `(D : ZMod 3) = 0`.
5. Convert back to `3 ∣ A`, `3 ∣ D`.
6. Contradict `E.hADcop` because it would imply `IsUnit (3 : ℤ)`.

Likely pasteable code:

```lean
namespace EulerSquarePair

theorem not_three_dvd_B (E : EulerSquarePair) : ¬ (3 : ℤ) ∣ E.B := by
  intro h3B

  have hBz :
      (E.B : ZMod 3) ^ 2 =
        (E.A : ZMod 3) ^ 2 + (E.D : ZMod 3) ^ 2 := by
    have h := congrArg (fun z : ℤ => (z : ZMod 3)) E.hB
    norm_num at h
    simpa using h

  have hB0 : (E.B : ZMod 3) = 0 := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd E.B 3).2 h3B

  have hsum : (E.A : ZMod 3) ^ 2 + (E.D : ZMod 3) ^ 2 = 0 := by
    simpa [hB0] using hBz.symm

  obtain ⟨hA0, hD0⟩ := zmod3_sq_add_sq_eq_zero hsum

  have h3A : (3 : ℤ) ∣ E.A := by
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd E.A 3).1 hA0
  have h3D : (3 : ℤ) ∣ E.D := by
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd E.D 3).1 hD0

  exact not_isUnit_three_int (E.hADcop h3A h3D)

end EulerSquarePair
```

If `norm_num at h` does not simplify the casted equation enough, replace the `hBz` block with this slightly more explicit variant:

```lean
  have hBz0 :
      (E.B : ZMod 3) ^ 2 =
        (16 : ZMod 3) * (E.A : ZMod 3) ^ 2 + (E.D : ZMod 3) ^ 2 := by
    exact_mod_cast E.hB
  have hBz :
      (E.B : ZMod 3) ^ 2 =
        (E.A : ZMod 3) ^ 2 + (E.D : ZMod 3) ^ 2 := by
    norm_num at hBz0 ⊢
    simpa using hBz0
```

## 4. Prove `3 ∤ C`

Same proof, using `E.hC`; `4 = 1` in `ZMod 3`.

```lean
namespace EulerSquarePair

theorem not_three_dvd_C (E : EulerSquarePair) : ¬ (3 : ℤ) ∣ E.C := by
  intro h3C

  have hCz :
      (E.C : ZMod 3) ^ 2 =
        (E.A : ZMod 3) ^ 2 + (E.D : ZMod 3) ^ 2 := by
    have h := congrArg (fun z : ℤ => (z : ZMod 3)) E.hC
    norm_num at h
    simpa using h

  have hC0 : (E.C : ZMod 3) = 0 := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd E.C 3).2 h3C

  have hsum : (E.A : ZMod 3) ^ 2 + (E.D : ZMod 3) ^ 2 = 0 := by
    simpa [hC0] using hCz.symm

  obtain ⟨hA0, hD0⟩ := zmod3_sq_add_sq_eq_zero hsum

  have h3A : (3 : ℤ) ∣ E.A := by
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd E.A 3).1 hA0
  have h3D : (3 : ℤ) ∣ E.D := by
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd E.D 3).1 hD0

  exact not_isUnit_three_int (E.hADcop h3A h3D)

end EulerSquarePair
```

## 5. Bridge to `IsCoprime` and multiply

After choosing the available prime bridge from §0, the final layer is short.

```lean
namespace EulerSquarePair

-- Local bridge target.  Implement with the available prime/coprime API.
-- Do not leave it as an axiom; this is a small theorem.
theorem isCoprime_three_int_of_not_dvd {x : ℤ}
    (hx : ¬ (3 : ℤ) ∣ x) : IsCoprime (3 : ℤ) x := by
  exact (show Prime (3 : ℤ) by norm_num).isCoprime_iff_not_dvd.mpr hx

theorem three_coprime_B (E : EulerSquarePair) : IsCoprime (3 : ℤ) E.B := by
  exact isCoprime_three_int_of_not_dvd (not_three_dvd_B E)

theorem three_coprime_C (E : EulerSquarePair) : IsCoprime (3 : ℤ) E.C := by
  exact isCoprime_three_int_of_not_dvd (not_three_dvd_C E)

theorem three_coprime_centerX (E : EulerSquarePair) :
    IsCoprime (3 : ℤ) E.centerX := by
  dsimp [centerX]
  exact (three_coprime_B E).mul_right (three_coprime_C E)

end EulerSquarePair
```

If `.isCoprime_iff_not_dvd` is not the method name, replace only the bridge theorem by the `.coprime_iff_not_dvd` variant:

```lean
theorem isCoprime_three_int_of_not_dvd {x : ℤ}
    (hx : ¬ (3 : ℤ) ∣ x) : IsCoprime (3 : ℤ) x := by
  exact (show Prime (3 : ℤ) by norm_num).coprime_iff_not_dvd.mpr hx
```

If both method names fail, keep the proven `not_three_dvd_B` and `not_three_dvd_C` and implement this exact helper by the divisor criterion:

```lean
theorem isCoprime_three_int_of_not_dvd {x : ℤ}
    (hx : ¬ (3 : ℤ) ∣ x) : IsCoprime (3 : ℤ) x
```

Proof route for the fallback helper:

```text
intro d hd3 hdx
Since `3` is prime and `d ∣ 3`, either `IsUnit d` or `Associated d 3`.
If `Associated d 3`, then `3 ∣ d`; with `d ∣ x`, get `3 ∣ x`, contradiction.
Therefore `IsUnit d`.
```

Search terms for that fallback are:

```lean
#check Prime.eq_or_eq_of_dvd_mul
#check Prime.dvd_or_dvd
#check Irreducible.isUnit_or_isUnit
#check Associated.dvd_iff_dvd_left
#check Associated.dvd_iff_dvd_right
```

## 6. Integer-mod alternative if ZMod casting is awkward

If the casted `ZMod` equations fight simplification, the same proof can be done with integer divisibility:

```text
Assume 3 | B.
From E.hB, 3 | B^2 and 3 | 15*A^2, so:
  B^2 = 16*A^2 + D^2
  ⇒ 3 | A^2 + D^2.
Modulo 3, use the integer residue lemma:
  3 | x^2 + y^2 ⇒ 3 | x ∧ 3 | y.
Then contradict E.hADcop.
```

Target helper for that route:

```lean
theorem three_dvd_sq_add_sq_iff {x y : ℤ} :
    (3 : ℤ) ∣ x ^ 2 + y ^ 2 ↔ (3 : ℤ) ∣ x ∧ (3 : ℤ) ∣ y
```

Proof should still use `ZMod.intCast_zmod_eq_zero_iff_dvd` internally plus `zmod3_sq_add_sq_eq_zero`; it just hides the casts from the main `not_three_dvd_B/C` proofs.

## Summary

The recommended implementation order is:

1. Add `zmod3_sq_add_sq_eq_zero`.
2. Add `not_isUnit_three_int`.
3. Prove `not_three_dvd_B` and `not_three_dvd_C` by casting `E.hB`, `E.hC` to `ZMod 3`.
4. Add the local bridge
   ```lean
   isCoprime_three_int_of_not_dvd {x : ℤ} :
     ¬ (3 : ℤ) ∣ x → IsCoprime (3 : ℤ) x
   ```
   using the available prime/coprime API.
5. Define `three_coprime_B`, `three_coprime_C`, and combine with `.mul_right` to get `three_coprime_centerX`.
