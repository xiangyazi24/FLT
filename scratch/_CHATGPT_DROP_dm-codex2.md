# Q2557 `EulerSquarePair` first gcd layer

This is a Lean-oriented plan for the first gcd layer in
`FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`, using the current structure fields exactly:

```lean
structure EulerSquarePair where
  A D B C : ℤ
  hApos : 0 < A
  hDpos : 0 < D
  hDodd : Odd D
  hAeven : Even A
  hADcop : IsCoprime A D
  hBpos : 0 < B
  hCpos : 0 < C
  hB : B ^ 2 = 16 * A ^ 2 + D ^ 2
  hC : C ^ 2 = 4 * A ^ 2 + D ^ 2
```

The target layer is:

```lean
theorem B_coprime_A (E : EulerSquarePair) : IsCoprime E.B E.A
theorem B_coprime_D (E : EulerSquarePair) : IsCoprime E.B E.D
theorem C_coprime_A (E : EulerSquarePair) : IsCoprime E.C E.A
theorem C_coprime_D (E : EulerSquarePair) : IsCoprime E.C E.D
theorem centerX_coprime_stepN (E : EulerSquarePair) : IsCoprime E.centerX E.stepN
```

No extra structure fields are needed.  The only real local arithmetic input beyond `E.hADcop` is using `E.hDodd` to prove that `D` is coprime to the numeric factors `4` and `16`.

## 0. API checks to run first

Before pasting the snippets, run these in the file or scratch buffer:

```lean
#check IsCoprime.symm
#check IsCoprime.pow_right
#check IsCoprime.pow_left
#check IsCoprime.mul_right
#check IsCoprime.mul_left
#check dvd_sub
#check dvd_add
```

Also check one of these odd/coprime-to-two APIs:

```lean
#check Odd.isCoprime_two
#check Odd.coprime_two
#check Int.not_even_iff_odd
```

The snippets below use the common `IsCoprime` divisor criterion style:

```lean
-- expected to elaborate if `IsCoprime` unfolds to the divisor criterion
example {a b d : ℤ} (h : IsCoprime a b) (ha : d ∣ a) (hb : d ∣ b) : IsUnit d := by
  exact h ha hb
```

If that example fails in your Mathlib snapshot, search/check the criterion name.  Likely candidates are:

```lean
#check IsCoprime.isUnit_of_dvd
#check IsRelPrime
#check isRelPrime_iff
```

Then replace applications like `h ha hb` by the corresponding method call.  Keep the theorem statements unchanged.

## 1. Tiny divisibility helper

This helper avoids depending on the exact name/signature of `dvd_pow`.

```lean
namespace EulerSquarePair

private theorem dvd_sq_of_dvd {d x : ℤ} (h : d ∣ x) : d ∣ x ^ 2 := by
  rw [pow_two]
  exact dvd_mul_of_dvd_left h x

end EulerSquarePair
```

## 2. The easy half: `B`/`C` coprime to `A`

These two lemmas should be the first ones to try.  They use only:

```text
B^2 = 16*A^2 + D^2,
C^2 = 4*A^2 + D^2,
IsCoprime A D,
IsCoprime.pow_right.
```

The idea is: a common divisor of `B` and `A` divides `B^2` and `16*A^2`, hence divides `D^2`; then `IsCoprime A (D^2)` makes it a unit.

```lean
namespace EulerSquarePair

theorem B_coprime_A (E : EulerSquarePair) : IsCoprime E.B E.A := by
  intro d hdB hdA
  have hdB2 : d ∣ E.B ^ 2 := dvd_sq_of_dvd hdB
  have hdA2 : d ∣ E.A ^ 2 := dvd_sq_of_dvd hdA
  have hd16A2 : d ∣ 16 * E.A ^ 2 := dvd_mul_of_dvd_right hdA2 16
  have hsum : d ∣ 16 * E.A ^ 2 + E.D ^ 2 := by
    rw [← E.hB]
    exact hdB2
  have hdD2 : d ∣ E.D ^ 2 := by
    have hsub : d ∣ (16 * E.A ^ 2 + E.D ^ 2) - 16 * E.A ^ 2 :=
      dvd_sub hsum hd16A2
    convert hsub using 1
    ring
  exact (E.hADcop.pow_right 2) hdA hdD2

theorem C_coprime_A (E : EulerSquarePair) : IsCoprime E.C E.A := by
  intro d hdC hdA
  have hdC2 : d ∣ E.C ^ 2 := dvd_sq_of_dvd hdC
  have hdA2 : d ∣ E.A ^ 2 := dvd_sq_of_dvd hdA
  have hd4A2 : d ∣ 4 * E.A ^ 2 := dvd_mul_of_dvd_right hdA2 4
  have hsum : d ∣ 4 * E.A ^ 2 + E.D ^ 2 := by
    rw [← E.hC]
    exact hdC2
  have hdD2 : d ∣ E.D ^ 2 := by
    have hsub : d ∣ (4 * E.A ^ 2 + E.D ^ 2) - 4 * E.A ^ 2 :=
      dvd_sub hsum hd4A2
    convert hsub using 1
    ring
  exact (E.hADcop.pow_right 2) hdA hdD2

end EulerSquarePair
```

If `E.hADcop.pow_right 2` does not elaborate, search:

```lean
#check IsCoprime.pow_right
#check IsCoprime.pow_left
```

The needed intermediate type is exactly:

```lean
have hAD2 : IsCoprime E.A (E.D ^ 2) := by
  -- from `E.hADcop`
```

## 3. The `D` side: isolate the parity/numeric-factor lemma

For `B_coprime_D` and `C_coprime_D`, a common divisor of `B` and `D` divides `16*A^2`, and a common divisor of `C` and `D` divides `4*A^2`.  Therefore isolate these two lemmas first:

```lean
namespace EulerSquarePair

-- Proposed intermediate theorem.
-- Prove from `E.hDodd` and `E.hADcop.symm.pow_right 2`.
theorem D_coprime_16A2_statement (E : EulerSquarePair) : Prop :=
  IsCoprime E.D (16 * E.A ^ 2)

-- Proposed intermediate theorem.
-- Prove from `E.hDodd` and `E.hADcop.symm.pow_right 2`.
theorem D_coprime_4A2_statement (E : EulerSquarePair) : Prop :=
  IsCoprime E.D (4 * E.A ^ 2)

end EulerSquarePair
```

Do not paste those two `*_statement` declarations if you want theorem names exactly `D_coprime_16A2` and `D_coprime_4A2`; they are shown this way only to avoid fake proofs in this note.  The actual theorem targets should be:

```lean
theorem D_coprime_16A2 (E : EulerSquarePair) : IsCoprime E.D (16 * E.A ^ 2)
theorem D_coprime_4A2  (E : EulerSquarePair) : IsCoprime E.D (4 * E.A ^ 2)
```

Proof DAG for `D_coprime_16A2`:

```text
E.hDodd
  ⇒ IsCoprime E.D (2 : ℤ)
  ⇒ IsCoprime E.D ((2 : ℤ)^4)
  ⇒ IsCoprime E.D (16 : ℤ)

E.hADcop.symm
  ⇒ IsCoprime E.D E.A
  ⇒ IsCoprime E.D (E.A^2)

combine with `IsCoprime.mul_right`
  ⇒ IsCoprime E.D (16 * E.A^2)
```

Proof DAG for `D_coprime_4A2` is identical with `(2 : ℤ)^2 = 4`.

Likely code once the odd-to-two API is found:

```lean
namespace EulerSquarePair

-- Sketch only: replace `ODD_TO_TWO_API E.hDodd` by the local API found by `#check`.
-- theorem D_coprime_16A2 (E : EulerSquarePair) : IsCoprime E.D (16 * E.A ^ 2) := by
--   have hD2 : IsCoprime E.D (2 : ℤ) := ODD_TO_TWO_API E.hDodd
--   have hD16 : IsCoprime E.D (16 : ℤ) := by
--     simpa using hD2.pow_right 4
--   have hDA2 : IsCoprime E.D (E.A ^ 2) := E.hADcop.symm.pow_right 2
--   simpa [mul_comm, mul_left_comm, mul_assoc] using hD16.mul_right hDA2
--
-- theorem D_coprime_4A2 (E : EulerSquarePair) : IsCoprime E.D (4 * E.A ^ 2) := by
--   have hD2 : IsCoprime E.D (2 : ℤ) := ODD_TO_TWO_API E.hDodd
--   have hD4 : IsCoprime E.D (4 : ℤ) := by
--     simpa using hD2.pow_right 2
--   have hDA2 : IsCoprime E.D (E.A ^ 2) := E.hADcop.symm.pow_right 2
--   simpa [mul_comm, mul_left_comm, mul_assoc] using hD4.mul_right hDA2

end EulerSquarePair
```

This is the one API-sensitive point in the layer.  It is not an extra hypothesis: it is a consequence of `hDodd`.

## 4. `B_coprime_D` and `C_coprime_D` once the numeric-factor lemmas exist

The following snippets are complete modulo the already-isolated lemmas `D_coprime_16A2` and `D_coprime_4A2`.

```lean
namespace EulerSquarePair

private theorem B_coprime_D_of_D_coprime_16A2
    (E : EulerSquarePair)
    (hD16A2 : IsCoprime E.D (16 * E.A ^ 2)) :
    IsCoprime E.B E.D := by
  intro d hdB hdD
  have hdB2 : d ∣ E.B ^ 2 := dvd_sq_of_dvd hdB
  have hdD2 : d ∣ E.D ^ 2 := dvd_sq_of_dvd hdD
  have hsum : d ∣ 16 * E.A ^ 2 + E.D ^ 2 := by
    rw [← E.hB]
    exact hdB2
  have hd16A2 : d ∣ 16 * E.A ^ 2 := by
    have hsub : d ∣ (16 * E.A ^ 2 + E.D ^ 2) - E.D ^ 2 :=
      dvd_sub hsum hdD2
    convert hsub using 1
    ring
  exact hD16A2 hdD hd16A2

private theorem C_coprime_D_of_D_coprime_4A2
    (E : EulerSquarePair)
    (hD4A2 : IsCoprime E.D (4 * E.A ^ 2)) :
    IsCoprime E.C E.D := by
  intro d hdC hdD
  have hdC2 : d ∣ E.C ^ 2 := dvd_sq_of_dvd hdC
  have hdD2 : d ∣ E.D ^ 2 := dvd_sq_of_dvd hdD
  have hsum : d ∣ 4 * E.A ^ 2 + E.D ^ 2 := by
    rw [← E.hC]
    exact hdC2
  have hd4A2 : d ∣ 4 * E.A ^ 2 := by
    have hsub : d ∣ (4 * E.A ^ 2 + E.D ^ 2) - E.D ^ 2 :=
      dvd_sub hsum hdD2
    convert hsub using 1
    ring
  exact hD4A2 hdD hd4A2

-- Final wrappers after proving the two numeric-factor lemmas:
-- theorem B_coprime_D (E : EulerSquarePair) : IsCoprime E.B E.D :=
--   B_coprime_D_of_D_coprime_16A2 E (D_coprime_16A2 E)
--
-- theorem C_coprime_D (E : EulerSquarePair) : IsCoprime E.C E.D :=
--   C_coprime_D_of_D_coprime_4A2 E (D_coprime_4A2 E)

end EulerSquarePair
```

## 5. Product coprimality: `centerX_coprime_stepN`

Once all four component lemmas are available, the clean proof is by `IsCoprime.mul_right` and `IsCoprime.mul_left`.

```lean
namespace EulerSquarePair

-- Paste after `B_coprime_A`, `B_coprime_D`, `C_coprime_A`, `C_coprime_D` are proved.
theorem centerX_coprime_stepN (E : EulerSquarePair) : IsCoprime E.centerX E.stepN := by
  dsimp [centerX, stepN]
  have hB_AD : IsCoprime E.B (E.A * E.D) := by
    exact (B_coprime_A E).mul_right (B_coprime_D E)
  have hC_AD : IsCoprime E.C (E.A * E.D) := by
    exact (C_coprime_A E).mul_right (C_coprime_D E)
  exact hB_AD.mul_left hC_AD

end EulerSquarePair
```

If the method orientation differs, the same proof normally becomes one of these:

```lean
-- exact IsCoprime.mul_left hB_AD hC_AD
-- exact IsCoprime.mul_right (B_coprime_A E) (B_coprime_D E)
```

Use the `#check IsCoprime.mul_left` / `#check IsCoprime.mul_right` output to select the method form.  The mathematical dependencies are exactly the four component lemmas above.

## 6. Next gcd layer among `fm6`, `fm2`, `fp2`, `fp6`

After `centerX_coprime_stepN`, the next target statements should be:

```lean
namespace EulerSquarePair

theorem fm2_coprime_fp2 (E : EulerSquarePair) : IsCoprime E.fm2 E.fp2 := by
  -- later proof
  -- common divisor divides `(fp2 + fm2) = 2*centerX`
  -- and `(fp2 - fm2) = 4*stepN`; oddness strips powers of 2;
  -- then use `centerX_coprime_stepN`.
  -- Do not paste until the odd-divisor stripping lemma is available.
  admit

theorem fm6_coprime_fp6 (E : EulerSquarePair) : IsCoprime E.fm6 E.fp6 := by
  -- later proof
  -- common divisor divides `2*centerX` and `12*stepN`;
  -- oddness strips 2, but a possible factor 3 remains.
  -- This needs the additional lemma `IsCoprime (3 : ℤ) E.centerX`.
  admit

theorem fm6_coprime_fm2 (E : EulerSquarePair) : IsCoprime E.fm6 E.fm2 := by
  -- later proof: difference is `4*stepN`, then use one factor to recover `centerX`.
  admit

theorem fm6_coprime_fp2 (E : EulerSquarePair) : IsCoprime E.fm6 E.fp2 := by
  -- later proof: difference is `8*stepN`.
  admit

theorem fm2_coprime_fp6 (E : EulerSquarePair) : IsCoprime E.fm2 E.fp6 := by
  -- later proof: difference is `8*stepN`.
  admit

theorem fp2_coprime_fp6 (E : EulerSquarePair) : IsCoprime E.fp2 E.fp6 := by
  -- later proof: difference is `4*stepN`.
  admit

end EulerSquarePair
```

The block above intentionally contains `admit` as a **non-pasteable target map**.  Do not insert it into the Lean file as-is.  The dependency DAG for the candidate-value gcds is:

```text
B_odd, C_odd, centerX_odd, stepN_even
  ⇒ fm6_odd, fm2_odd, fp2_odd, fp6_odd

odd common divisor + divisor of 2*k
  ⇒ divisor of k

centerX_coprime_stepN
  ⇒ all cross gcds except outer pair are straightforward

three_coprime_centerX : IsCoprime (3 : ℤ) E.centerX
  ⇒ fm6_coprime_fp6
```

For the odd-divisor stripping helper, aim for a reusable statement like:

```lean
-- Proposed helper, statement only.
-- If an odd integer `m` is divisible by `d`, then `d` is coprime to `2`.
-- Therefore `d ∣ 2*k` implies `d ∣ k` by `IsCoprime.dvd_of_dvd_mul_left/right`.
```

The exact API to search here is:

```lean
#check IsCoprime.dvd_of_dvd_mul_left
#check IsCoprime.dvd_of_dvd_mul_right
#check Odd.isCoprime_two
#check Odd.coprime_two
```

## Summary

The recommended implementation order is:

1. Add `dvd_sq_of_dvd`.
2. Prove `B_coprime_A` and `C_coprime_A` using the pasteable snippets above.
3. Prove `D_coprime_16A2` and `D_coprime_4A2` from `hDodd` and `hADcop.symm.pow_right 2`.
4. Use the `*_of_D_coprime_*` snippets to finish `B_coprime_D` and `C_coprime_D`.
5. Combine them with `IsCoprime.mul_right`/`mul_left` to prove `centerX_coprime_stepN`.
6. Only then start the six gcd facts among `fm6`, `fm2`, `fp2`, `fp6`; the outer pair additionally needs `IsCoprime (3 : ℤ) E.centerX`.
