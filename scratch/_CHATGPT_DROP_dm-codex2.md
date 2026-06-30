# Q2551 EulerSquarePairToPrimitiveCentered reconstruction theorem DAG

This note answers the narrow reconstruction problem:

```lean
def EulerSquarePairToPrimitiveCentered : Prop :=
  ∀ E : EulerSquarePair, ∃ T : PrimitiveCenteredFourSqAP, T.N = E.A * E.D
```

The already checked identities are exactly the right algebraic inputs:

```lean
eulerPair_middle_product_square:
  (B*C)^2 - (2*(A*D))^2 = (D^2 + 8*A^2)^2

eulerPair_outer_product_square:
  (B*C)^2 - (6*(A*D))^2 = (D^2 - 8*A^2)^2
```

The missing work is not more `ring`.  It is the integer reconstruction step:

```text
X := B*C,  N := A*D
X - 6*N, X - 2*N, X + 2*N, X + 6*N
```

are positive, odd, pairwise coprime square values.  Once that is isolated, the final constructor for `PrimitiveCenteredFourSqAP` is short.

## 0. Minimal fields needed on `EulerSquarePair`

For the exact reconstruction with `X = E.B * E.C`, the structure must provide or make derivable the following data:

```lean
structure EulerSquarePair where
  A D B C : ℤ
  hApos : 0 < A
  hDpos : 0 < D
  hAeven : Even A
  hDodd : Odd D
  hADcop : Int.gcd A D = 1
  hBpos : 0 < B
  hCpos : 0 < C
  hBsq : B ^ 2 = 16 * A ^ 2 + D ^ 2
  hCsq : C ^ 2 = 4 * A ^ 2 + D ^ 2
```

If the current structure lacks `hBpos` and `hCpos`, add them or define the reconstruction with normalized roots

```lean
B₊ := |E.B|
C₊ := |E.C|
X  := B₊ * C₊
```

instead.  With only square equations for `B` and `C`, the statement using literally `X = E.B * E.C` is sign-sensitive and can fail when one of `B,C` is negative.  Since the requested target explicitly says `X = B*C`, the minimal honest addition is `hBpos : 0 < B` and `hCpos : 0 < C` if they are missing.

Do **not** add the following as fields; prove them as lemmas from the fields above:

```text
Odd B, Odd C, Odd X, Even N,
gcd(B*C, A*D)=1,
gcd(3, B*C)=1,
0 < X - 6*N,
pairwise gcd of the four square values.
```

## 1. Local notation

Inside `N12FourSquaresAP.lean`, add local definitions to keep the final proof readable.

```lean
namespace EulerSquarePair

@[simp] def centerX (E : EulerSquarePair) : ℤ := E.B * E.C
@[simp] def stepN   (E : EulerSquarePair) : ℤ := E.A * E.D

@[simp] def fm6 (E : EulerSquarePair) : ℤ := E.centerX - 6 * E.stepN
@[simp] def fm2 (E : EulerSquarePair) : ℤ := E.centerX - 2 * E.stepN
@[simp] def fp2 (E : EulerSquarePair) : ℤ := E.centerX + 2 * E.stepN
@[simp] def fp6 (E : EulerSquarePair) : ℤ := E.centerX + 6 * E.stepN

end EulerSquarePair
```

The final AP should use

```lean
T.X = E.centerX
T.N = E.stepN
p^2 = E.fm6
q^2 = E.fm2
r^2 = E.fp2
s^2 = E.fp6
```

where `p,q,r,s` are chosen positive and odd.

## 2. Generic integer square-factor lemmas

The key generic lemma is the standard one already requested in the earlier coprime-square-product task:

```lean
theorem Int_coprime_mul_eq_sq_of_nonneg
    {a b z : ℤ}
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hcop : Int.gcd a b = 1)
    (h : a * b = z ^ 2) :
    ∃ r s : ℤ, a = r ^ 2 ∧ b = s ^ 2 := by
  -- Existing/planned reusable number-theory lemma.
  -- Prove by prime valuations or by natAbs + Nat coprime square factor theorem.
  sorry
```

For this reconstruction, use a slightly stronger wrapper that normalizes signs and records oddness.

```lean
theorem Int.exists_pos_odd_sq_factors_of_coprime_mul_eq_sq
    {a b z : ℤ}
    (ha : 0 < a)
    (hb : 0 < b)
    (haodd : Odd a)
    (hbodd : Odd b)
    (hcop : Int.gcd a b = 1)
    (hmul : a * b = z ^ 2) :
    ∃ r s : ℤ,
      0 < r ∧ 0 < s ∧
      Odd r ∧ Odd s ∧
      r ^ 2 = a ∧ s ^ 2 = b ∧
      Int.gcd r s = 1 := by
  obtain ⟨r0, s0, hr0, hs0⟩ :=
    Int_coprime_mul_eq_sq_of_nonneg (le_of_lt ha) (le_of_lt hb) hcop hmul
  -- Choose positive roots by absolute value.
  -- r := |r0|, s := |s0|.
  -- Positivity follows from `a > 0`, `b > 0`.
  -- Oddness follows from `a`/`b` odd and `a = r0^2`, `b = s0^2`.
  -- Coprimality of roots follows from coprimality of their squares.
  sorry
```

Also isolate the root-gcd descent, because it is needed for cross-gcd fields of `PrimitiveCenteredFourSqAP`.

```lean
theorem Int.gcd_eq_one_of_sq_gcd_eq_one
    {x y : ℤ}
    (h : Int.gcd (x ^ 2) (y ^ 2) = 1) :
    Int.gcd x y = 1 := by
  -- Prime divisor proof, or natAbs + Nat.Coprime.pow.
  sorry

theorem Int.root_gcd_of_square_values_gcd
    {x y fx fy : ℤ}
    (hx : x ^ 2 = fx)
    (hy : y ^ 2 = fy)
    (h : Int.gcd fx fy = 1) :
    Int.gcd x y = 1 := by
  apply Int.gcd_eq_one_of_sq_gcd_eq_one
  simpa [hx, hy] using h
```

These three lemmas should live near the other reusable integer lemmas, not inside the final constructor proof.

## 3. Euler-pair consequences

The following lemmas are the exact local number-theory obligations needed before applying the square-factor lemma.

### 3.1 Positivity and parity of `X,N`

```lean
namespace EulerSquarePair

theorem stepN_pos (E : EulerSquarePair) : 0 < E.stepN := by
  dsimp [stepN]
  nlinarith [E.hApos, E.hDpos]

theorem stepN_even (E : EulerSquarePair) : Even E.stepN := by
  rcases E.hAeven with ⟨a, ha⟩
  refine ⟨a * E.D, ?_⟩
  dsimp [stepN]
  rw [ha]
  ring

theorem B_odd (E : EulerSquarePair) : Odd E.B := by
  -- `A` even makes `16*A^2` even; `D` odd makes `D^2` odd.
  -- So the RHS of `hBsq` is odd, hence `B^2` odd, hence `B` odd.
  sorry

theorem C_odd (E : EulerSquarePair) : Odd E.C := by
  -- Same proof using `hCsq` and `4*A^2 + D^2`.
  sorry

theorem centerX_pos (E : EulerSquarePair) : 0 < E.centerX := by
  dsimp [centerX]
  nlinarith [E.hBpos, E.hCpos]

theorem centerX_odd (E : EulerSquarePair) : Odd E.centerX := by
  dsimp [centerX]
  exact (E.B_odd.mul E.C_odd)

end EulerSquarePair
```

If the current names are `hB`/`hC` rather than `hBsq`/`hCsq`, only the field names above need to be adjusted.

### 3.2 Coprimality of `X` and `N`

Do not try to prove all factor gcds directly.  First prove:

```lean
namespace EulerSquarePair

theorem B_coprime_A (E : EulerSquarePair) : Int.gcd E.B E.A = 1 := by
  -- If a prime divides `B` and `A`, then from
  -- `B^2 = 16*A^2 + D^2` it divides `D`, contradicting `gcd A D = 1`.
  sorry

theorem B_coprime_D (E : EulerSquarePair) : Int.gcd E.B E.D = 1 := by
  -- If a prime divides `B` and `D`, then it divides `16*A^2`.
  -- Since `D` is odd, no factor 2 issue remains; conclude it divides `A`.
  sorry

theorem C_coprime_A (E : EulerSquarePair) : Int.gcd E.C E.A = 1 := by
  -- Same argument with `C^2 = 4*A^2 + D^2`.
  sorry

theorem C_coprime_D (E : EulerSquarePair) : Int.gcd E.C E.D = 1 := by
  -- Same argument with `C^2 = 4*A^2 + D^2`.
  sorry

theorem centerX_coprime_stepN (E : EulerSquarePair) :
    Int.gcd E.centerX E.stepN = 1 := by
  -- Combine the four preceding gcd facts by multiplicativity/coprime product lemmas.
  -- Equivalently use prime divisors: any prime dividing `B*C` and `A*D`
  -- divides one of B,C and one of A,D, contradiction.
  sorry

end EulerSquarePair
```

### 3.3 The necessary mod-3 fact for the outer pair

For the middle pair, `gcd(X - 2N, X + 2N)` only has a possible odd divisor of `2`, so parity kills it.  For the outer pair, the difference is `12N`, so a possible extra divisor `3` must be excluded.

Prove the following once:

```lean
namespace EulerSquarePair

theorem three_coprime_centerX (E : EulerSquarePair) :
    Int.gcd (3 : ℤ) E.centerX = 1 := by
  -- It is enough to show `3 ∤ B` and `3 ∤ C`.
  -- Modulo 3, both square equations become
  --   B^2 ≡ A^2 + D^2,
  --   C^2 ≡ A^2 + D^2.
  -- If 3 divided B or C, then A^2 + D^2 ≡ 0 mod 3.
  -- Over ZMod 3, this forces both A and D divisible by 3,
  -- contradicting `E.hADcop`.
  sorry

end EulerSquarePair
```

This is not an extra field.  It is derivable and should be part of the reconstruction theorem family.

## 4. Product-square identities in factor form

Turn the two checked identities into the product forms consumed by the square-factor lemma.

```lean
namespace EulerSquarePair

theorem middle_factor_product_square (E : EulerSquarePair) :
    E.fm2 * E.fp2 = (E.D ^ 2 + 8 * E.A ^ 2) ^ 2 := by
  dsimp [fm2, fp2, centerX, stepN]
  calc
    (E.B * E.C - 2 * (E.A * E.D)) *
        (E.B * E.C + 2 * (E.A * E.D))
        = (E.B * E.C) ^ 2 - (2 * (E.A * E.D)) ^ 2 := by ring
    _ = (E.D ^ 2 + 8 * E.A ^ 2) ^ 2 := by
      exact eulerPair_middle_product_square E.hBsq E.hCsq

theorem outer_factor_product_square (E : EulerSquarePair) :
    E.fm6 * E.fp6 = (E.D ^ 2 - 8 * E.A ^ 2) ^ 2 := by
  dsimp [fm6, fp6, centerX, stepN]
  calc
    (E.B * E.C - 6 * (E.A * E.D)) *
        (E.B * E.C + 6 * (E.A * E.D))
        = (E.B * E.C) ^ 2 - (6 * (E.A * E.D)) ^ 2 := by ring
    _ = (E.D ^ 2 - 8 * E.A ^ 2) ^ 2 := by
      exact eulerPair_outer_product_square E.hBsq E.hCsq

end EulerSquarePair
```

Adjust the calls if the checked identities are currently theorems with `(E : EulerSquarePair)` as the first argument rather than raw `hBsq hCsq` arguments.

## 5. Positivity of all four factors

The only nontrivial one is `X - 6N > 0`.  Once this is available, all other positivity facts are immediate.

```lean
namespace EulerSquarePair

theorem Dsq_sub_8Asq_ne_zero (E : EulerSquarePair) :
    E.D ^ 2 - 8 * E.A ^ 2 ≠ 0 := by
  -- Parity proof: `D^2` is odd, `8*A^2` is even.
  -- Hence their difference is odd, in particular nonzero.
  sorry

theorem fm6_pos (E : EulerSquarePair) : 0 < E.fm6 := by
  have hprod := E.outer_factor_product_square
  have hright_pos : 0 < (E.D ^ 2 - 8 * E.A ^ 2) ^ 2 := by
    exact sq_pos_of_ne_zero (E.Dsq_sub_8Asq_ne_zero)
  have hplus : 0 < E.fp6 := by
    dsimp [fp6, centerX, stepN]
    nlinarith [E.centerX_pos, E.stepN_pos]
  -- From `(fm6)*(fp6) = positive` and `fp6 > 0`, get `fm6 > 0`.
  nlinarith [hprod, hright_pos, hplus]

theorem fm2_pos (E : EulerSquarePair) : 0 < E.fm2 := by
  dsimp [fm2, fm6, stepN] at *
  have hN := E.stepN_pos
  have h6 := E.fm6_pos
  nlinarith

theorem fp2_pos (E : EulerSquarePair) : 0 < E.fp2 := by
  dsimp [fp2, stepN]
  nlinarith [E.centerX_pos, E.stepN_pos]

theorem fp6_pos (E : EulerSquarePair) : 0 < E.fp6 := by
  dsimp [fp6, stepN]
  nlinarith [E.centerX_pos, E.stepN_pos]

end EulerSquarePair
```

If `nlinarith` does not close `fm6_pos`, replace the last step with the ordered-domain lemma:

```lean
theorem pos_of_mul_pos_right_int {a b : ℤ} (h : 0 < a * b) (hb : 0 < b) : 0 < a := by
  nlinarith [mul_pos_iff.mp h]
```

or prove it by cases on `a ≤ 0`.

## 6. Oddness of the four factors

```lean
namespace EulerSquarePair

theorem fm6_odd (E : EulerSquarePair) : Odd E.fm6 := by
  -- odd X minus even 6N.
  dsimp [fm6]
  exact E.centerX_odd.sub (Even.mul_left _ E.stepN_even)

theorem fm2_odd (E : EulerSquarePair) : Odd E.fm2 := by
  dsimp [fm2]
  exact E.centerX_odd.sub (Even.mul_left _ E.stepN_even)

theorem fp2_odd (E : EulerSquarePair) : Odd E.fp2 := by
  dsimp [fp2]
  exact E.centerX_odd.add (Even.mul_left _ E.stepN_even)

theorem fp6_odd (E : EulerSquarePair) : Odd E.fp6 := by
  dsimp [fp6]
  exact E.centerX_odd.add (Even.mul_left _ E.stepN_even)

end EulerSquarePair
```

The exact lemma names for `Odd.add`, `Odd.sub`, and `Even.mul_left` may differ slightly in the local Mathlib snapshot.  If so, keep the theorem statements and prove them by expanding `Odd`/`Even` witnesses.

## 7. GCDs of the square values

These are the central arithmetic lemmas.  They should be separate from square-root extraction.

```lean
namespace EulerSquarePair

theorem fm2_fp2_gcd (E : EulerSquarePair) :
    Int.gcd E.fm2 E.fp2 = 1 := by
  -- Any common odd divisor divides both
  --   (fm2 + fp2) = 2*X
  --   (fp2 - fm2) = 4*N.
  -- Since both factors are odd, it divides X and N.
  -- Use `centerX_coprime_stepN`.
  sorry

theorem fm6_fp6_gcd (E : EulerSquarePair) :
    Int.gcd E.fm6 E.fp6 = 1 := by
  -- Any common odd divisor divides 2*X and 12*N.
  -- Using gcd(X,N)=1, only a divisor of 3 can remain.
  -- Exclude that using `three_coprime_centerX`.
  sorry

theorem fm6_fm2_gcd (E : EulerSquarePair) : Int.gcd E.fm6 E.fm2 = 1 := by
  -- Difference is 4*N; common odd divisor also divides X.
  sorry

theorem fm6_fp2_gcd (E : EulerSquarePair) : Int.gcd E.fm6 E.fp2 = 1 := by
  -- Difference is 8*N; common odd divisor also divides X.
  sorry

theorem fm2_fp6_gcd (E : EulerSquarePair) : Int.gcd E.fm2 E.fp6 = 1 := by
  -- Difference is 8*N; common odd divisor also divides X.
  sorry

theorem fp2_fp6_gcd (E : EulerSquarePair) : Int.gcd E.fp2 E.fp6 = 1 := by
  -- Difference is 4*N; common odd divisor also divides X.
  sorry

end EulerSquarePair
```

The proof pattern for the four cross-gcds is easier than the outer pair: their differences are powers of two times `N`, and all four factors are odd, so no prime divisor of `2` can occur.  The outer pair is the only place where the divisor `3` must be excluded.

## 8. Extract roots for the middle and outer pairs

Now apply the generic square-factor lemma twice.

```lean
namespace EulerSquarePair

theorem middle_roots (E : EulerSquarePair) :
    ∃ q r : ℤ,
      0 < q ∧ 0 < r ∧
      Odd q ∧ Odd r ∧
      q ^ 2 = E.fm2 ∧ r ^ 2 = E.fp2 ∧
      Int.gcd q r = 1 := by
  exact Int.exists_pos_odd_sq_factors_of_coprime_mul_eq_sq
    E.fm2_pos E.fp2_pos E.fm2_odd E.fp2_odd
    E.fm2_fp2_gcd E.middle_factor_product_square

theorem outer_roots (E : EulerSquarePair) :
    ∃ p s : ℤ,
      0 < p ∧ 0 < s ∧
      Odd p ∧ Odd s ∧
      p ^ 2 = E.fm6 ∧ s ^ 2 = E.fp6 ∧
      Int.gcd p s = 1 := by
  exact Int.exists_pos_odd_sq_factors_of_coprime_mul_eq_sq
    E.fm6_pos E.fp6_pos E.fm6_odd E.fp6_odd
    E.fm6_fp6_gcd E.outer_factor_product_square

end EulerSquarePair
```

Notice the sign choice: the roots returned by `Int_coprime_mul_eq_sq_of_nonneg` are normalized by absolute value in the wrapper.  Thus the final `p,q,r,s` are positive.  There is no need to decide the sign of `D^2 - 8*A^2`; it is only the product root `p*s` up to sign.

## 9. Combine into a root package with all pairwise gcds

It is useful to introduce one local data structure.  This keeps the final `PrimitiveCenteredFourSqAP` constructor readable and makes the pairwise gcd obligations explicit.

```lean
structure EulerCenteredRootData (E : EulerSquarePair) where
  p q r s : ℤ
  hp_pos : 0 < p
  hq_pos : 0 < q
  hr_pos : 0 < r
  hs_pos : 0 < s
  hp_odd : Odd p
  hq_odd : Odd q
  hr_odd : Odd r
  hs_odd : Odd s
  hp_sq : p ^ 2 = E.fm6
  hq_sq : q ^ 2 = E.fm2
  hr_sq : r ^ 2 = E.fp2
  hs_sq : s ^ 2 = E.fp6
  hpq : Int.gcd p q = 1
  hpr : Int.gcd p r = 1
  hps : Int.gcd p s = 1
  hqr : Int.gcd q r = 1
  hqs : Int.gcd q s = 1
  hrs : Int.gcd r s = 1
```

Constructor theorem:

```lean
namespace EulerSquarePair

theorem centeredRootData (E : EulerSquarePair) :
    EulerCenteredRootData E := by
  obtain ⟨p, s, hp_pos, hs_pos, hp_odd, hs_odd, hp_sq, hs_sq, hps⟩ :=
    E.outer_roots
  obtain ⟨q, r, hq_pos, hr_pos, hq_odd, hr_odd, hq_sq, hr_sq, hqr⟩ :=
    E.middle_roots

  have hpq : Int.gcd p q = 1 :=
    Int.root_gcd_of_square_values_gcd hp_sq hq_sq E.fm6_fm2_gcd
  have hpr : Int.gcd p r = 1 :=
    Int.root_gcd_of_square_values_gcd hp_sq hr_sq E.fm6_fp2_gcd
  have hqs : Int.gcd q s = 1 :=
    Int.root_gcd_of_square_values_gcd hq_sq hs_sq E.fm2_fp6_gcd
  have hrs : Int.gcd r s = 1 :=
    Int.root_gcd_of_square_values_gcd hr_sq hs_sq E.fp2_fp6_gcd

  exact
    { p := p, q := q, r := r, s := s
      hp_pos := hp_pos, hq_pos := hq_pos, hr_pos := hr_pos, hs_pos := hs_pos
      hp_odd := hp_odd, hq_odd := hq_odd, hr_odd := hr_odd, hs_odd := hs_odd
      hp_sq := hp_sq, hq_sq := hq_sq, hr_sq := hr_sq, hs_sq := hs_sq
      hpq := hpq, hpr := hpr, hps := hps, hqr := hqr, hqs := hqs, hrs := hrs }

end EulerSquarePair
```

If the `PrimitiveCenteredFourSqAP` structure uses `IsCoprime` fields instead of `Int.gcd _ _ = 1`, add wrappers once:

```lean
theorem isCoprime_of_int_gcd_eq_one {a b : ℤ} (h : Int.gcd a b = 1) :
    IsCoprime a b := by
  -- local compatibility wrapper, depending on the current Mathlib gcd API
  sorry
```

## 10. Final reconstruction theorem

The final theorem should be only a constructor from `centeredRootData`.

```lean
namespace EulerSquarePair

theorem toPrimitiveCentered (E : EulerSquarePair) :
    ∃ T : PrimitiveCenteredFourSqAP, T.N = E.A * E.D := by
  let R := E.centeredRootData
  refine ⟨
    { N := E.stepN
      X := E.centerX
      p := R.p
      q := R.q
      r := R.r
      s := R.s

      -- main AP square equations
      hp := by
        -- field name may be `hp_sq`; adapt to current structure
        simpa [EulerSquarePair.fm6, EulerSquarePair.centerX, EulerSquarePair.stepN]
          using R.hp_sq
      hq := by
        simpa [EulerSquarePair.fm2, EulerSquarePair.centerX, EulerSquarePair.stepN]
          using R.hq_sq
      hr := by
        simpa [EulerSquarePair.fp2, EulerSquarePair.centerX, EulerSquarePair.stepN]
          using R.hr_sq
      hs := by
        simpa [EulerSquarePair.fp6, EulerSquarePair.centerX, EulerSquarePair.stepN]
          using R.hs_sq

      -- positivity, if `PrimitiveCenteredFourSqAP` has these fields
      hp_pos := R.hp_pos
      hq_pos := R.hq_pos
      hr_pos := R.hr_pos
      hs_pos := R.hs_pos
      hNpos := E.stepN_pos

      -- odd root fields
      hp_odd := R.hp_odd
      hq_odd := R.hq_odd
      hr_odd := R.hr_odd
      hs_odd := R.hs_odd

      -- pairwise gcd fields
      hpq := R.hpq
      hpr := R.hpr
      hps := R.hps
      hqr := R.hqr
      hqs := R.hqs
      hrs := R.hrs },
    by
      dsimp [EulerSquarePair.stepN]
  ⟩

theorem EulerSquarePairToPrimitiveCentered_proof :
    EulerSquarePairToPrimitiveCentered := by
  intro E
  exact E.toPrimitiveCentered

end EulerSquarePair
```

The constructor field names in the block above should be mechanically adjusted to the current `PrimitiveCenteredFourSqAP` names.  The intended mapping is unambiguous:

```text
p^2 = X - 6N
q^2 = X - 2N
r^2 = X + 2N
s^2 = X + 6N
N   = A*D
X   = B*C
```

## 11. Suggested patch order

Implement in this order to keep each compile failure local:

1. Add local notation `centerX`, `stepN`, `fm6`, `fm2`, `fp2`, `fp6`.
2. Add or confirm the minimal `EulerSquarePair` fields.  For exact `X=B*C`, `hBpos` and `hCpos` are required unless the theorem internally normalizes `B,C` by absolute value.
3. Add the generic integer wrappers:
   - `Int.exists_pos_odd_sq_factors_of_coprime_mul_eq_sq`
   - `Int.gcd_eq_one_of_sq_gcd_eq_one`
   - `Int.root_gcd_of_square_values_gcd`
4. Prove Euler-pair parity and coprimality consequences:
   - `B_odd`, `C_odd`, `centerX_odd`, `stepN_even`
   - `centerX_coprime_stepN`
   - `three_coprime_centerX`
5. Convert the checked algebra identities into factor-product identities:
   - `middle_factor_product_square`
   - `outer_factor_product_square`
6. Prove positivity:
   - `Dsq_sub_8Asq_ne_zero`
   - `fm6_pos`, then `fm2_pos`, `fp2_pos`, `fp6_pos`
7. Prove the six square-value gcds.
8. Extract `outer_roots` and `middle_roots`.
9. Build `EulerCenteredRootData`.
10. Finish `EulerSquarePair.toPrimitiveCentered` and the wrapper theorem for `EulerSquarePairToPrimitiveCentered`.

## 12. Main caution

Do not try to set

```text
q = D^2 + 8*A^2
p = D^2 - 8*A^2
```

or any similar explicit formula.  The checked identities only prove

```text
(X - 2N)(X + 2N) = (D^2 + 8A^2)^2
(X - 6N)(X + 6N) = (D^2 - 8A^2)^2
```

The individual square roots of `X ± 2N` and `X ± 6N` come from positivity plus coprimality of the two factors in each product.  The correct Lean shape is therefore existential root extraction, followed by sign normalization with absolute value.
