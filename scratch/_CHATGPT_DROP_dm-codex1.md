# Q2515 corrected raw Euler factor refinement

## Fix summary

The three local failures from Q2504 are real and should be fixed as follows.

1. Do **not** write multiple structure fields on one line in this file.  Use one field per line:
   ```lean
   alpha : ℤ
   b : ℤ
   c : ℤ
   d : ℤ
   ```
   This avoids the dependent-field parse that made `alpha` look like a function.

2. Do **not** prove the integer row helper by rewriting `U` with a casted equality and then calling `simp`; that rewrites `U` inside the gcd arguments.  Use a `calc` chain and cast the Nat equality with `congrArg`.

3. Avoid the missing `gcd_pos_of_ne_zero_left`.  The helper `int_gcd_pos_of_left_pos` below proves positivity directly from `Nat.gcd_dvd_left` and `Int.natAbs_eq_zero`.

Below is the corrected no-`sorry`, no-`axiom` patch.

```lean
import Mathlib.Tactic
import Mathlib.Data.Int.GCD
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
  alpha : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
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

/-- Positivity of the integer gcd cast, proved without relying on the unavailable
`gcd_pos_of_ne_zero_left` name. -/
theorem int_gcd_pos_of_left_pos {a b : ℤ} (ha : 0 < a) :
    0 < (Int.gcd a b : ℤ) := by
  have hg_ne : Int.gcd a b ≠ 0 := by
    intro hg
    have hdvd : Int.gcd a b ∣ a.natAbs := by
      rw [Int.gcd_def]
      exact Nat.gcd_dvd_left _ _
    have ha_abs_zero : a.natAbs = 0 := by
      rw [hg] at hdvd
      simpa using hdvd
    have ha_zero : a = 0 := Int.natAbs_eq_zero.mp ha_abs_zero
    exact (ne_of_gt ha) ha_zero
  have hg_pos_nat : 0 < Int.gcd a b := Nat.pos_of_ne_zero hg_ne
  exact_mod_cast hg_pos_nat

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

/-- Integer row identity, transported through `natAbs`.

The proof deliberately avoids rewriting `U` in-place, because that rewrites inside
`Int.gcd U U'` and `Int.gcd U V'`. -/
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
      Nat.gcd U.natAbs U'.natAbs * Nat.gcd U.natAbs V'.natAbs = U.natAbs :=
    nat_rowU_gcd_mul_gcd_of_mul_eq_mul_of_coprime hmulN hcopN
  calc
    U = (U.natAbs : ℤ) :=
      (Int.natAbs_of_nonneg (le_of_lt hUpos)).symm
    _ = ((Nat.gcd U.natAbs U'.natAbs * Nat.gcd U.natAbs V'.natAbs : ℕ) : ℤ) :=
      congrArg (fun n : ℕ => (n : ℤ)) hrowN.symm
    _ = (Nat.gcd U.natAbs U'.natAbs : ℤ) *
        (Nat.gcd U.natAbs V'.natAbs : ℤ) := by
      rw [Int.natCast_mul]
    _ = (Int.gcd U U' : ℤ) * (Int.gcd U V' : ℤ) := by
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
    exact int_gcd_pos_of_left_pos hUpos
  have hb_pos : 0 < b := by
    dsimp [b]
    exact int_gcd_pos_of_left_pos hUpos
  have hc_pos : 0 < c := by
    dsimp [c]
    exact int_gcd_pos_of_left_pos hVpos
  have hd_pos : 0 < d := by
    dsimp [d]
    exact int_gcd_pos_of_left_pos hVpos
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

If anything still fails locally, isolate the first three theorems (`int_gcd_pos_of_left_pos`, `nat_rowU_gcd_mul_gcd_of_mul_eq_mul_of_coprime`, and `int_rowU_gcd_mul_gcd_of_two_factorizations`) first.  They are independent of the final raw structure package and directly fix the row-helper rewrite bug.
