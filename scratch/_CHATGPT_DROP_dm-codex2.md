# Q2201 dm-codex2 — N=12 dual 2-squareclass local obstruction

## Verdict

The stated theorem is mathematically correct as written:

```lean
theorem n12_dual_two_squareclass_no_solution
    (m n W : ℤ) (hcop : Int.gcd m n = 1) :
    W ^ 2 ≠ 2 * m ^ 4 - 4 * m ^ 2 * n ^ 2 + 8 * n ^ 4
```

No additional nonzero hypothesis is needed. The gcd hypothesis already excludes `(m,n)=(0,0)`, and the remaining primitive parity cases are killed modulo `16`.

The proof is exactly the advertised local obstruction. For coprime integers, the parity pairs are:

```text
m odd,  n odd  -> RHS ≡  2 - 4 + 8 = 6 mod 16,
m odd,  n even -> RHS ≡  2         = 2 mod 16,
m even, n odd  -> RHS ≡          8 = 8 mod 16,
m even, n even -> impossible from gcd(m,n)=1.
```

Integer squares modulo `16` are only

```text
0, 1, 4, 9.
```

So `2`, `6`, and `8` are impossible.

If `hcop` is removed, the exact statement is false because `(m,n,W)=(0,0,0)` solves it. If one keeps `m,n` nonzero but drops primitivity, the mod-16 proof no longer directly closes the both-even case; one would then use a 2-adic infinite descent or reduce to the primitive pair. For the requested primitive homogeneous-space lemma, no correction is needed.

## Recommended Lean shape

Use `ZMod 16`. This avoids fighting with `Int.emod` normalization across the whole theorem. The only delicate point is the helper converting `Int.gcd m n = 1` into “not both even”. I recommend isolating that as a tiny lemma; the rest is finite arithmetic.

Put this under:

```lean
namespace MazurProof.RationalPointsN12
```

with imports adjusted to the local file. The snippet below uses `import Mathlib` to be paste-safe.

## Paste-oriented Lean snippets

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

abbrev Z16 := ZMod 16

/-!
Local obstruction for the dual 2-isogeny descent on
  F' : Y^2 = X^3 - 4 X^2 + 16 X.
The squareclass `2` would force
  W^2 = 2*m^4 - 4*m^2*n^2 + 8*n^4,
which is impossible modulo 16 for primitive `(m,n)`.
-/

private lemma z16_square_residue (x : Z16) :
    x ^ 2 = 0 ∨ x ^ 2 = 1 ∨ x ^ 2 = 4 ∨ x ^ 2 = 9 := by
  fin_cases x <;> norm_num

private lemma z16_square_ne_two (x : Z16) : x ^ 2 ≠ 2 := by
  intro h
  rcases z16_square_residue x with h0 | h1 | h4 | h9
  · rw [h0] at h; norm_num at h
  · rw [h1] at h; norm_num at h
  · rw [h4] at h; norm_num at h
  · rw [h9] at h; norm_num at h

private lemma z16_square_ne_six (x : Z16) : x ^ 2 ≠ 6 := by
  intro h
  rcases z16_square_residue x with h0 | h1 | h4 | h9
  · rw [h0] at h; norm_num at h
  · rw [h1] at h; norm_num at h
  · rw [h4] at h; norm_num at h
  · rw [h9] at h; norm_num at h

private lemma z16_square_ne_eight (x : Z16) : x ^ 2 ≠ 8 := by
  intro h
  rcases z16_square_residue x with h0 | h1 | h4 | h9
  · rw [h0] at h; norm_num at h
  · rw [h1] at h; norm_num at h
  · rw [h4] at h; norm_num at h
  · rw [h9] at h; norm_num at h

/-- Odd fourth powers are `1 mod 16`. Useful elsewhere, but the final proof
below can also use the more direct RHS lemmas. -/
private lemma z16_fourth_of_odd {x : ℤ} (hx : Odd x) :
    ((x : Z16) ^ 4) = 1 := by
  rcases hx with ⟨k, rfl⟩
  -- `ring_nf` alone may leave a parity-valued term; split the parity of `k`.
  rcases Int.even_or_odd k with hk | hk
  · rcases hk with ⟨t, rfl⟩
    ring_nf
  · rcases hk with ⟨t, rfl⟩
    ring_nf

/-- Even fourth powers are `0 mod 16`. -/
private lemma z16_fourth_of_even {x : ℤ} (hx : Even x) :
    ((x : Z16) ^ 4) = 0 := by
  rcases hx with ⟨k, rfl⟩
  ring_nf

/-- If `m` and `n` are coprime integers, they are not both even.

The exact API name for converting `Int.gcd = 1` to `IsCoprime` has moved
across mathlib versions. In current-style mathlib, one of the commented lines
usually works. Keeping this as a separate lemma localizes that brittleness. -/
private lemma not_even_even_of_int_gcd_eq_one
    {m n : ℤ} (hcop : Int.gcd m n = 1) : ¬ (Even m ∧ Even n) := by
  intro h
  rcases h with ⟨hm, hn⟩

  -- Preferred proof if the `Int.gcd` / `IsCoprime` bridge is available:
  --
  -- have hcop' : IsCoprime m n := by
  --   exact (Int.gcd_eq_one_iff_coprime.mp hcop)
  -- -- Alternative spellings seen in nearby mathlib versions:
  -- --   simpa [Int.isCoprime_iff_gcd_eq_one] using hcop
  -- --   exact (Int.isCoprime_iff_gcd_eq_one.mpr hcop)
  -- have hunit : IsUnit (2 : ℤ) := hcop'.isUnit_of_dvd hm hn
  -- norm_num at hunit

  -- GCD-only fallback: expand even witnesses and use `Int.gcd_mul_left`.
  rcases hm with ⟨r, rfl⟩
  rcases hn with ⟨s, rfl⟩
  have hg : Int.gcd (r + r) (s + s) = 2 * Int.gcd r s := by
    rw [show r + r = 2 * r by ring, show s + s = 2 * s by ring]
    -- Depending on the local mathlib, this may be named `Int.gcd_mul_left`
    -- or require a `simpa [mul_comm, mul_left_comm, mul_assoc]` wrapper.
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Int.gcd_mul_left r s 2)
  rw [hg] at hcop
  omega

/-- RHS modulo 16 when `m` is odd and `n` is even. -/
private lemma n12_dual_rhs_mod16_odd_even
    {m n : ℤ} (hm : Odd m) (hn : Even n) :
    (((2 * m ^ 4 - 4 * m ^ 2 * n ^ 2 + 8 * n ^ 4 : ℤ) : Z16) = 2) := by
  rcases hm with ⟨r, rfl⟩
  rcases hn with ⟨s, rfl⟩
  -- After the parity substitution the difference from `2` has all
  -- coefficients divisible by `16`.
  ring_nf

/-- RHS modulo 16 when `m` is even and `n` is odd. -/
private lemma n12_dual_rhs_mod16_even_odd
    {m n : ℤ} (hm : Even m) (hn : Odd n) :
    (((2 * m ^ 4 - 4 * m ^ 2 * n ^ 2 + 8 * n ^ 4 : ℤ) : Z16) = 8) := by
  rcases hm with ⟨r, rfl⟩
  rcases hn with ⟨s, rfl⟩
  ring_nf

/-- RHS modulo 16 when both `m` and `n` are odd. -/
private lemma n12_dual_rhs_mod16_odd_odd
    {m n : ℤ} (hm : Odd m) (hn : Odd n) :
    (((2 * m ^ 4 - 4 * m ^ 2 * n ^ 2 + 8 * n ^ 4 : ℤ) : Z16) = 6) := by
  rcases hm with ⟨r, rfl⟩
  rcases hn with ⟨s, rfl⟩
  ring_nf

/-- The dual-descent local obstruction ruling out squareclass `2`. -/
theorem n12_dual_two_squareclass_no_solution
    (m n W : ℤ) (hcop : Int.gcd m n = 1) :
    W ^ 2 ≠ 2 * m ^ 4 - 4 * m ^ 2 * n ^ 2 + 8 * n ^ 4 := by
  intro h

  -- Cast the assumed integer equality to `ZMod 16`.
  have hZ : (W : Z16) ^ 2 =
      ((2 * m ^ 4 - 4 * m ^ 2 * n ^ 2 + 8 * n ^ 4 : ℤ) : Z16) := by
    have hcast := congrArg (fun t : ℤ => (t : Z16)) h
    simpa using hcast

  by_cases hmEven : Even m
  · by_cases hnEven : Even n
    · exact (not_even_even_of_int_gcd_eq_one hcop) ⟨hmEven, hnEven⟩
    · have hnOdd : Odd n := not_even_iff_odd.mp hnEven
      have hrhs := n12_dual_rhs_mod16_even_odd (m := m) (n := n) hmEven hnOdd
      exact z16_square_ne_eight (W : Z16) (hZ.trans hrhs)
  · have hmOdd : Odd m := not_even_iff_odd.mp hmEven
    by_cases hnEven : Even n
    · have hrhs := n12_dual_rhs_mod16_odd_even (m := m) (n := n) hmOdd hnEven
      exact z16_square_ne_two (W : Z16) (hZ.trans hrhs)
    · have hnOdd : Odd n := not_even_iff_odd.mp hnEven
      have hrhs := n12_dual_rhs_mod16_odd_odd (m := m) (n := n) hmOdd hnOdd
      exact z16_square_ne_six (W : Z16) (hZ.trans hrhs)

end MazurProof.RationalPointsN12
```

## If `Int.even_or_odd` or `not_even_iff_odd` names differ

The parity API is the most likely source of minor breakage. The proof can be rewritten to avoid global parity lemmas by using `by_cases h : Even x`; the odd branch is then obtained by whichever local theorem is available:

```lean
have hxOdd : Odd x := not_even_iff_odd.mp hxEven
```

If that exact theorem name fails, try one of:

```lean
exact Nat.not_even_iff_odd.mp hxEven       -- for naturals only
exact Int.not_even_iff_odd.mp hxEven
simpa [Int.not_even_iff] using hxEven
```

For `Int.even_or_odd k` inside `z16_fourth_of_odd`, an easy fallback is:

```lean
by_cases hkEven : Even k
· rcases hkEven with ⟨t, rfl⟩
  ring_nf
· have hkOdd : Odd k := not_even_iff_odd.mp hkEven
  rcases hkOdd with ⟨t, rfl⟩
  ring_nf
```

## Even-even gcd helper alternatives

If `Int.gcd_mul_left` is not available with the exact argument order above, use the `IsCoprime` route. It is conceptually cleaner:

```lean
private lemma not_even_even_of_int_gcd_eq_one_via_isCoprime
    {m n : ℤ} (hcop : Int.gcd m n = 1) : ¬ (Even m ∧ Even n) := by
  intro h
  have hcop' : IsCoprime m n := by
    -- Use the spelling available in the checked mathlib revision:
    -- exact (Int.gcd_eq_one_iff_coprime.mp hcop)
    -- or
    -- exact (Int.isCoprime_iff_gcd_eq_one.mpr hcop)
    -- or bridge through `Nat.Coprime` on `natAbs`.
    sorry
  have hunit : IsUnit (2 : ℤ) := hcop'.isUnit_of_dvd h.1 h.2
  norm_num at hunit
```

Another robust fallback avoids `IsCoprime` but uses natAbs/gcd lemmas:

```lean
private lemma not_even_even_of_int_gcd_eq_one_via_natAbs
    {m n : ℤ} (hcop : Int.gcd m n = 1) : ¬ (Even m ∧ Even n) := by
  intro h
  rcases h.1 with ⟨r, rfl⟩
  rcases h.2 with ⟨s, rfl⟩
  have hg : Int.gcd (r + r) (s + s) = 2 * Int.gcd r s := by
    rw [show r + r = 2*r by ring, show s + s = 2*s by ring]
    -- Usually:
    -- simpa [mul_comm, mul_left_comm, mul_assoc] using Int.gcd_mul_left r s 2
    sorry
  rw [hg] at hcop
  omega
```

I would keep the final theorem independent of which bridge is chosen by naming the local helper `not_even_even_of_int_gcd_eq_one` and making the final proof depend only on that.

## Alternative Int.ModEq style

If the file already uses `%` / `Int.emod` rather than `ZMod`, the same proof can be phrased through `Int.ModEq`:

```lean
-- Square residues:
--   W^2 % 16 ∈ {0,1,4,9}
-- RHS residues:
--   odd/even -> RHS ≡ 2 [ZMOD 16]
--   even/odd -> RHS ≡ 8 [ZMOD 16]
--   odd/odd  -> RHS ≡ 6 [ZMOD 16]
```

I do not recommend this as the first implementation because `Int.ModEq` proofs tend to require more manual divisibility rewriting. `ZMod 16` plus `fin_cases` is shorter and less brittle.

## Minimal lemma DAG for the file

1. `z16_square_residue`:

   ```lean
   private lemma z16_square_residue (x : ZMod 16) :
       x^2 = 0 ∨ x^2 = 1 ∨ x^2 = 4 ∨ x^2 = 9
   ```

2. Derived contradictions:

   ```lean
   private lemma z16_square_ne_two   (x : ZMod 16) : x^2 ≠ 2
   private lemma z16_square_ne_six   (x : ZMod 16) : x^2 ≠ 6
   private lemma z16_square_ne_eight (x : ZMod 16) : x^2 ≠ 8
   ```

3. Optional reusable power lemmas:

   ```lean
   private lemma z16_fourth_of_odd  {x : ℤ} (hx : Odd x)  : ((x : ZMod 16)^4) = 1
   private lemma z16_fourth_of_even {x : ℤ} (hx : Even x) : ((x : ZMod 16)^4) = 0
   ```

4. Primitive parity helper:

   ```lean
   private lemma not_even_even_of_int_gcd_eq_one
       {m n : ℤ} (hcop : Int.gcd m n = 1) : ¬ (Even m ∧ Even n)
   ```

5. RHS residue lemmas:

   ```lean
   private lemma n12_dual_rhs_mod16_odd_even  ... : RHS = 2 in ZMod 16
   private lemma n12_dual_rhs_mod16_even_odd  ... : RHS = 8 in ZMod 16
   private lemma n12_dual_rhs_mod16_odd_odd   ... : RHS = 6 in ZMod 16
   ```

6. Main theorem:

   ```lean
   theorem n12_dual_two_squareclass_no_solution
       (m n W : ℤ) (hcop : Int.gcd m n = 1) :
       W ^ 2 ≠ 2 * m ^ 4 - 4 * m ^ 2 * n ^ 2 + 8 * n ^ 4
   ```

## Brittle spots to expect

- The spelling of the `Int.gcd = 1` to `IsCoprime` bridge may differ in the pinned mathlib revision. Isolate it.
- `Even` witnesses may unfold as `x = k + k`, not `x = 2*k`; `ring_nf` handles both, but explicit rewrites should use `show k + k = 2*k by ring` if needed.
- `z16_fourth_of_odd` is not a pure `ring` identity after substituting `x=2*k+1`; split the parity of `k`, or avoid this lemma and prove the three RHS residue lemmas directly.
- The final cast step should be `congrArg (fun t : ℤ => (t : ZMod 16)) h` followed by `simpa`; if `simpa` does not push powers, try `simpa [map_pow] using hcast`.
- Do not replace `ZMod 16` by `ZMod 8`: the odd/odd case gives `6 mod 16`, which is `6 mod 8`; squares mod 8 are `0,1,4`, so it would still work, but the advertised standard obstruction and the even/odd residue split are cleaner at modulus `16`.
