# Q2504 raw Euler factor refinement

## Verdict

The full raw theorem is the right next lemma, and it is not necessary to stop at only the `U` row.  The key Mathlib API is:

```lean
Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime
```

It gives, for coprime `n m`,

```lean
Nat.gcd x n * Nat.gcd x m = x ↔ x ∣ n * m
```

Applying this to the natural absolute values proves the row identity

```lean
U = (Int.gcd U U' : ℤ) * (Int.gcd U V' : ℤ)
```

from `A = U*V = U'*V'` and `IsCoprime U' V'`.  The other three row/column identities follow by swapping the two factorizations and/or swapping the two factors in a product.  Pairwise coprimality of the four gcd-intersection factors is then a direct `IsCoprime.mono` argument.

Below is the intended no-`sorry`, no-`axiom` Lean code.

```lean
import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.RingTheory.Int.Basic

structure PairwiseCoprime2abcd (a b c d : ℤ) : Prop where
  hab : IsCoprime a b
  hac : IsCoprime a c
  had : IsCoprime a d
  hbc : IsCoprime b c
  hbd : IsCoprime b d
  hcd : IsCoprime c d

structure RawRefinedFactors (A U V U' V' : ℤ) where
  alpha b c d : ℤ
  halpha_pos : 0 < alpha
  hb_pos : 0 < b
  hc_pos : 0 < c
  hd_pos : 0 < d
  hU : U = alpha * b
  hV : V = c * d
  hU' : U' = alpha * c
  hV' : V' = b * d
  hA : A = alpha * b * c * d
  hpair : PairwiseCoprime2abcd alpha b c d

/-- Natural-number row identity: if `U*V = U'*V'` and `U'` is coprime to `V'`,
then the `U` row splits as `gcd U U' * gcd U V'`. -/
theorem nat_rowU_gcd_mul_gcd_of_mul_eq_mul_of_coprime
    {U V U' V' : ℕ}
    (hmul : U * V = U' * V')
    (hcop : Nat.Coprime U' V') :
    Nat.gcd U U' * Nat.gcd U V' = U := by
  exact
    (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime
      (x := U) (n := U') (m := V') hcop).2 ⟨V, hmul.symm⟩

/-- Integer row identity, transported through `natAbs`.  This is the main reusable
helper for each row/column of the raw refinement. -/
theorem int_rowU_gcd_mul_gcd_of_two_factorizations
    {A U V U' V' : ℤ}
    (hUV : A = U * V)
    (hU'V' : A = U' * V')
    (hUpos : 0 < U)
    (hU'V'cop : IsCoprime U' V') :
    U = (Int.gcd U U' : ℤ) * (Int.gcd U V' : ℤ) := by
  have hmulZ : U * V = U' * V' := hUV.symm.trans hU'V'
  have hmulN : U.natAbs * V.natAbs = U'.natAbs * V'.natAbs := by
    simpa [Int.natAbs_mul] using congrArg Int.natAbs hmulZ
  have hcopN : Nat.Coprime U'.natAbs V'.natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hU'V'cop
  have hrowN :
      Nat.gcd U.natAbs U'.natAbs * Nat.gcd U.natAbs V'.natAbs = U.natAbs := by
    exact nat_rowU_gcd_mul_gcd_of_mul_eq_mul_of_coprime hmulN hcopN
  have hrowZ :
      ((Nat.gcd U.natAbs U'.natAbs * Nat.gcd U.natAbs V'.natAbs : ℕ) : ℤ) = U := by
    rw [hrowN, Int.natAbs_of_nonneg (le_of_lt hUpos)]
  rw [← hrowZ]
  simp [Int.gcd_def]

/-- Raw refinement of two positive coprime factorizations.

The four factors are the four gcd intersections:

* `alpha = gcd U U'`
* `b     = gcd U V'`
* `c     = gcd V U'`
* `d     = gcd V V'`
-/
theorem two_coprime_factorizations_refine_raw_pos
    {A U V U' V' : ℤ}
    (hUV : A = U * V)
    (hU'V' : A = U' * V')
    (hUpos : 0 < U) (hVpos : 0 < V)
    (hU'pos : 0 < U') (hV'pos : 0 < V')
    (hUVcop : IsCoprime U V)
    (hU'V'cop : IsCoprime U' V') :
    Nonempty (RawRefinedFactors A U V U' V') := by
  let alpha : ℤ := (Int.gcd U U' : ℤ)
  let b : ℤ := (Int.gcd U V' : ℤ)
  let c : ℤ := (Int.gcd V U' : ℤ)
  let d : ℤ := (Int.gcd V V' : ℤ)
  have hUrow : U = alpha * b := by
    dsimp [alpha, b]
    exact int_rowU_gcd_mul_gcd_of_two_factorizations hUV hU'V' hUpos hU'V'cop
  have hVU : A = V * U := by
    rw [mul_comm]
    exact hUV
  have hVrow : V = c * d := by
    dsimp [c, d]
    exact int_rowU_gcd_mul_gcd_of_two_factorizations hVU hU'V' hVpos hU'V'cop
  have hU'row0 : U' = (Int.gcd U' U : ℤ) * (Int.gcd U' V : ℤ) :=
    int_rowU_gcd_mul_gcd_of_two_factorizations hU'V' hUV hU'pos hUVcop
  have hU'row : U' = alpha * c := by
    dsimp [alpha, c]
    simpa [Int.gcd_def, Nat.gcd_comm] using hU'row0
  have hV'U' : A = V' * U' := by
    rw [mul_comm]
    exact hU'V'
  have hV'row0 : V' = (Int.gcd V' U : ℤ) * (Int.gcd V' V : ℤ) :=
    int_rowU_gcd_mul_gcd_of_two_factorizations hV'U' hUV hV'pos hUVcop
  have hV'row : V' = b * d := by
    dsimp [b, d]
    simpa [Int.gcd_def, Nat.gcd_comm] using hV'row0
  have halpha_pos : 0 < alpha := by
    dsimp [alpha]
    exact_mod_cast (gcd_pos_of_ne_zero_left U' (ne_of_gt hUpos) : 0 < Int.gcd U U')
  have hb_pos : 0 < b := by
    dsimp [b]
    exact_mod_cast (gcd_pos_of_ne_zero_left V' (ne_of_gt hUpos) : 0 < Int.gcd U V')
  have hc_pos : 0 < c := by
    dsimp [c]
    exact_mod_cast (gcd_pos_of_ne_zero_left U' (ne_of_gt hVpos) : 0 < Int.gcd V U')
  have hd_pos : 0 < d := by
    dsimp [d]
    exact_mod_cast (gcd_pos_of_ne_zero_left V' (ne_of_gt hVpos) : 0 < Int.gcd V V')
  have hpair : PairwiseCoprime2abcd alpha b c d := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp [alpha, b]
      exact IsCoprime.mono (Int.gcd_dvd_right U U') (Int.gcd_dvd_right U V') hU'V'cop
    · dsimp [alpha, c]
      exact IsCoprime.mono (Int.gcd_dvd_left U U') (Int.gcd_dvd_left V U') hUVcop
    · dsimp [alpha, d]
      exact IsCoprime.mono (Int.gcd_dvd_right U U') (Int.gcd_dvd_right V V') hU'V'cop
    · dsimp [b, c]
      exact IsCoprime.mono (Int.gcd_dvd_left U V') (Int.gcd_dvd_left V U') hUVcop
    · dsimp [b, d]
      exact IsCoprime.mono (Int.gcd_dvd_left U V') (Int.gcd_dvd_left V V') hUVcop
    · dsimp [c, d]
      exact IsCoprime.mono (Int.gcd_dvd_right V U') (Int.gcd_dvd_right V V') hU'V'cop
  refine ⟨{
    alpha := alpha
    b := b
    c := c
    d := d
    halpha_pos := halpha_pos
    hb_pos := hb_pos
    hc_pos := hc_pos
    hd_pos := hd_pos
    hU := hUrow
    hV := hVrow
    hU' := hU'row
    hV' := hV'row
    hA := ?_
    hpair := hpair
  }⟩
  calc
    A = U * V := hUV
    _ = (alpha * b) * (c * d) := by rw [hUrow, hVrow]
    _ = alpha * b * c * d := by ring
```

## Notes

The row helper is the main point of the patch.  Once it is available, the full raw refinement is symmetric:

```lean
U  = gcd U U'  * gcd U V'
V  = gcd V U'  * gcd V V'
U' = gcd U' U  * gcd U' V
V' = gcd V' U  * gcd V' V
```

The `simpa [Int.gcd_def, Nat.gcd_comm]` calls convert the last two rows into the chosen names `alpha*c` and `b*d`.

The pairwise coprimality fields are all monotonicity consequences.  For example `alpha` divides `U'`, `b` divides `V'`, and `IsCoprime U' V'`; hence `IsCoprime alpha b` by `IsCoprime.mono`.
