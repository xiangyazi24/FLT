# Q2659: Eisenstein triple parametrization audit

Target file: `FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean`.
This note is independent of elliptic curves and `RationalPointsN12`.

## Verdict

The proposed theorem is **false as stated**. The exceptional primitive positive triple

```lean
(X, Y, Z) = (1, 1, 1)
```

satisfies

```lean
Z ^ 2 = X ^ 2 - X * Y + Y ^ 2
0 < X, 0 < Y, 0 < Z, Int.gcd X Y = 1
```

but it cannot satisfy the requested parametrization with `0 < n ∧ n < m`: the equation
`Z = m ^ 2 - m * n + n ^ 2 = 1` has no solution with `0 < n < m` that also gives
`X = Y = 1` through the displayed formulas.

Use this corrected statement instead:

```lean
theorem eisensteinTriple_primitive_param_or_unit
    {X Y Z : ℤ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hcop : Int.gcd X Y = 1)
    (hE : EisensteinTriple X Y Z) :
    (X = 1 ∧ Y = 1 ∧ Z = 1) ∨
      ∃ m n : ℤ, 0 < n ∧ n < m ∧ Int.gcd m n = 1 ∧ ¬ (3 : ℤ) ∣ m + n ∧
        EisensteinParam X Y Z m n
```

Equivalently, if the caller already knows `X ≠ Y`, then the original existential conclusion is valid:

```lean
theorem eisensteinTriple_primitive_param_of_ne
    {X Y Z : ℤ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hcop : Int.gcd X Y = 1) (hXY : X ≠ Y)
    (hE : EisensteinTriple X Y Z) :
    ∃ m n : ℤ, 0 < n ∧ n < m ∧ Int.gcd m n = 1 ∧ ¬ (3 : ℤ) ∣ m + n ∧
      EisensteinParam X Y Z m n
```

## Recommended imports and APIs

```lean
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic
```

Useful APIs to `#check`/grep:

```lean
#check PythagoreanTriple.coprime_classification
#check PythagoreanTriple.coprime_classification'
#check PythagoreanTriple.classification
#check Int.sq_of_gcd_eq_one
#check Int.sq_of_isCoprime
#check Int.isCoprime_iff_gcd_eq_one
#check Nat.Prime.not_coprime_iff_dvd
#check Int.Prime.dvd_natAbs_of_coe_dvd_sq
#check Int.natCast_dvd
#check Int.ModEq
#check Int.modEq_iff_dvd
#check Int.emod_two_eq_zero_or_one
#check Int.odd_iff
#check Int.not_even_iff_odd
#check Int.two_dvd_mul_add_one
#check eq_or_eq_neg_of_sq_eq_sq
```

`PythagoreanTriples` is a good model for the rational-parametrization style, but it does **not** directly classify
`x ^ 2 + 3 * y ^ 2 = z ^ 2`. For this theorem, the most Lean-friendly route is the elementary
factorization of

```lean
(2 * Z - (2 * X - Y)) * (2 * Z + (2 * X - Y)) = 3 * Y ^ 2
```

when `Y` is odd, and the symmetric argument when `X` is odd.

## Definitions

```lean
namespace MazurProof.QuarticEisenstein

def EisensteinTriple (X Y Z : ℤ) : Prop :=
  Z ^ 2 = X ^ 2 - X * Y + Y ^ 2

def EisensteinParam (X Y Z m n : ℤ) : Prop :=
  Z = m ^ 2 - m * n + n ^ 2 ∧
  ((X = m ^ 2 - n ^ 2 ∧ Y = 2 * m * n - n ^ 2) ∨
   (Y = m ^ 2 - n ^ 2 ∧ X = 2 * m * n - n ^ 2))
```

## First easy lemmas

These are direct and should compile with `ring`/`nlinarith` after minor local namespace adjustment.

```lean
lemma EisensteinParam.triple {X Y Z m n : ℤ}
    (h : EisensteinParam X Y Z m n) :
    EisensteinTriple X Y Z := by
  rcases h with ⟨hZ, hXY | hYX⟩
  · rcases hXY with ⟨hX, hY⟩
    subst Z; subst X; subst Y
    unfold EisensteinTriple
    ring
  · rcases hYX with ⟨hY, hX⟩
    subst Z; subst X; subst Y
    unfold EisensteinTriple
    ring

lemma EisensteinTriple.symm {X Y Z : ℤ}
    (h : EisensteinTriple X Y Z) : EisensteinTriple Y X Z := by
  unfold EisensteinTriple at h ⊢
  nlinarith

lemma EisensteinParam.symm {X Y Z m n : ℤ}
    (h : EisensteinParam X Y Z m n) : EisensteinParam Y X Z m n := by
  rcases h with ⟨hZ, hXY | hYX⟩
  · exact ⟨hZ, Or.inr ⟨hXY.1, hXY.2⟩⟩
  · exact ⟨hZ, Or.inl ⟨hYX.1, hYX.2⟩⟩
```

The unit exception is also worth isolating:

```lean
lemma EisensteinTriple.unit_of_eq
    {X Y Z : ℤ} (hX : 0 < X) (hZ : 0 < Z)
    (hcop : Int.gcd X Y = 1) (hE : EisensteinTriple X Y Z)
    (hXY : X = Y) : X = 1 ∧ Y = 1 ∧ Z = 1 := by
  subst Y
  unfold EisensteinTriple at hE
  have hZsq : Z ^ 2 = X ^ 2 := by nlinarith
  have hZX : Z = X := by
    rcases eq_or_eq_neg_of_sq_eq_sq Z X hZsq with h | h
    · exact h
    · nlinarith
  subst Z
  have hXabs : X.natAbs = 1 := by
    -- Usually:
    --   simpa [Int.gcd_self] using hcop
    -- If `Int.gcd_self` is not found in this import set, prove it by
    -- `Nat.dvd_antisymm` from `Int.gcd_dvd_left/right` and `Int.dvd_coe_gcd`.
    sorry
  have hX1 : X = 1 := by
    have hnonneg : 0 ≤ X := le_of_lt hX
    -- `Int.natAbs_inj_of_nonneg_of_nonneg` is available from `Mathlib.Data.Int.Lemmas`.
    -- Alternatively `omega` closes this after `have : (X.natAbs : ℤ) = 1 := by exact_mod_cast hXabs`.
    have : (X.natAbs : ℤ) = 1 := by exact_mod_cast hXabs
    omega
  exact ⟨hX1, hX1, hX1⟩
```

## Odd-second branch: the main local classification

The plan is to prove the parametrization when the second coordinate is odd. If the original `Y` is
even, primitive coprimality forces `X` odd, so run this lemma on the swapped triple and then use
`EisensteinParam.symm`.

```lean
private def P (X Y Z : ℤ) : ℤ := 2 * Z - (2 * X - Y)
private def Q (X Y Z : ℤ) : ℤ := 2 * Z + (2 * X - Y)

lemma eisenstein_factor_identity {X Y Z : ℤ}
    (hE : EisensteinTriple X Y Z) :
    P X Y Z * Q X Y Z = 3 * Y ^ 2 := by
  unfold P Q EisensteinTriple at hE ⊢
  nlinarith

lemma eisenstein_factor_pos_left {X Y Z : ℤ}
    (hY : 0 < Y) (hZ : 0 < Z) (hE : EisensteinTriple X Y Z) :
    0 < P X Y Z := by
  unfold P
  -- Use `(2*Z)^2 - (2*X-Y)^2 = 3*Y^2 > 0`, hence `abs (2*X-Y) < 2*Z`.
  -- If `2*X-Y ≤ 0`, this is immediate; otherwise compare squares with `sq_lt_sq`.
  sorry

lemma eisenstein_factor_pos_right {X Y Z : ℤ}
    (hY : 0 < Y) (hZ : 0 < Z) (hE : EisensteinTriple X Y Z) :
    0 < Q X Y Z := by
  unfold Q
  -- Same proof as `eisenstein_factor_pos_left`, using `-(2*X-Y) < 2*Z`.
  sorry

lemma eisenstein_factor_odd_left {X Y Z : ℤ}
    (hYodd : Odd Y) : Odd (P X Y Z) := by
  unfold P
  -- `2*Z - 2*X` is even; even + odd is odd.
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    ((even_two_mul (Z - X)).add_odd hYodd)

lemma eisenstein_factor_odd_right {X Y Z : ℤ}
    (hYodd : Odd Y) : Odd (Q X Y Z) := by
  unfold Q
  -- `2*Z + 2*X` is even; even - odd is odd.
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    ((even_two_mul (Z + X)).add_odd hYodd)
```

The next lemma chooses the correct mod-3 sign. This is where the exceptional unit is used. Without
excluding `(1,1,1)`, it is false: for `(1,1,1)`, `P = 1` and `Q = 3`.

```lean
lemma three_dvd_P_of_primitive_odd_second_nonunit
    {X Y Z : ℤ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hcop : Int.gcd X Y = 1) (hYodd : Odd Y)
    (hE : EisensteinTriple X Y Z)
    (hnotunit : ¬ (X = 1 ∧ Y = 1 ∧ Z = 1)) :
    (3 : ℤ) ∣ P X Y Z := by
  -- Work modulo 3.
  -- From `hE`, `Z^2 ≡ (X+Y)^2 [ZMOD 3]`.
  -- Hence `3 ∣ Z - (X+Y)` or `3 ∣ Z + (X+Y)`.
  -- The second sign implies the unit case under positivity + primitivity; rule it out by `hnotunit`.
  -- Then `3 ∣ Z - X - Y`, equivalent by `ring` to `3 ∣ 2*Z - (2*X - Y)`.
  -- APIs: `Int.modEq_iff_dvd`, `Int.ModEq.pow`, `Int.ModEq.add`, `Int.ModEq.sub`, `norm_num`.
  sorry
```

Now extract squares from the factorization. This is the core lemma to make robust. It should use
`Int.sq_of_gcd_eq_one` exactly as in your other square-extraction work.

```lean
lemma coprime_P_div3_Q_of_primitive_odd_second
    {X Y Z : ℤ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hcop : Int.gcd X Y = 1) (hYodd : Odd Y)
    (hE : EisensteinTriple X Y Z)
    (hP3 : (3 : ℤ) ∣ P X Y Z) :
    Int.gcd (P X Y Z / 3) (Q X Y Z) = 1 := by
  -- Prime-divisor proof.
  -- Assume a Nat prime `p` divides both. Cast to Int with `Int.natCast_dvd`.
  -- Use `P*Q = 3*Y^2`, the definitions of `P,Q`, and `hcop` to force `p ∣ X` and `p ∣ Y`, contradiction.
  -- For `p = 3`, use the chosen sign `hP3` and primitive/nonunit sign lemma to show `¬3 ∣ Q`.
  -- APIs: `Nat.Prime.not_coprime_iff_dvd`, `Int.Prime.dvd_natAbs_of_coe_dvd_sq`,
  -- `Int.dvd_coe_gcd`, `Int.natCast_dvd`, `Int.gcd_dvd_left`, `Int.gcd_dvd_right`.
  sorry

lemma square_extraction_odd_second
    {X Y Z : ℤ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hcop : Int.gcd X Y = 1) (hYodd : Odd Y)
    (hE : EisensteinTriple X Y Z)
    (hnotunit : ¬ (X = 1 ∧ Y = 1 ∧ Z = 1)) :
    ∃ n t : ℤ,
      0 < n ∧ 0 < t ∧ Odd n ∧ Odd t ∧ Int.gcd n t = 1 ∧
      P X Y Z = 3 * n ^ 2 ∧ Q X Y Z = t ^ 2 ∧ Y = n * t := by
  have hP3 : (3 : ℤ) ∣ P X Y Z :=
    three_dvd_P_of_primitive_odd_second_nonunit hX hY hZ hcop hYodd hE hnotunit
  have hPpos : 0 < P X Y Z := eisenstein_factor_pos_left hY hZ hE
  have hQpos : 0 < Q X Y Z := eisenstein_factor_pos_right hY hZ hE
  have hPQ : P X Y Z * Q X Y Z = 3 * Y ^ 2 := eisenstein_factor_identity hE
  have hcopPQ : Int.gcd (P X Y Z / 3) (Q X Y Z) = 1 :=
    coprime_P_div3_Q_of_primitive_odd_second hX hY hZ hcop hYodd hE hP3
  have hprod : (P X Y Z / 3) * Q X Y Z = Y ^ 2 := by
    -- Use `hP3` to rewrite `P = 3 * (P/3)`, then cancel 3 in `hPQ`.
    have hPdiv : 3 * (P X Y Z / 3) = P X Y Z := by
      exact (Int.ediv_mul_cancel hP3).symm
    nlinarith
  obtain ⟨n0, hn0 | hn0⟩ := Int.sq_of_gcd_eq_one hcopPQ hprod
  · obtain ⟨t0, ht0 | ht0⟩ := Int.sq_of_gcd_eq_one (by simpa [Int.gcd_comm] using hcopPQ) (by simpa [mul_comm] using hprod)
    · let n := |n0|
      let t := |t0|
      refine ⟨n, t, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- `0 < n` from `P/3 > 0` and `P/3 = n0^2`.
        sorry
      · -- `0 < t` from `Q > 0` and `Q = t0^2`.
        sorry
      · -- Oddness from `P` odd and `P = 3*n^2`.
        sorry
      · -- Oddness from `Q` odd and `Q = t^2`.
        sorry
      · -- gcd from `hcopPQ`, after `abs`.
        sorry
      · calc
          P X Y Z = 3 * (P X Y Z / 3) := by rw [Int.ediv_mul_cancel hP3, mul_comm]
          _ = 3 * n ^ 2 := by
            -- `hn0 : P/3 = n0^2`, `n = |n0|`.
            simp [n, hn0, sq_abs]
      · calc
          Q X Y Z = t ^ 2 := by
            -- `ht0 : Q = t0^2`, `t = |t0|`.
            simp [t, ht0, sq_abs]
      · -- From `Y^2 = (n*t)^2` and positivity, `Y = n*t`.
        have hYsq : Y ^ 2 = (n * t) ^ 2 := by
          -- combine `hprod`, `hn0`, `ht0`.
          sorry
        rcases eq_or_eq_neg_of_sq_eq_sq Y (n * t) hYsq with h | h
        · exact h
        · have hntpos : 0 < n * t := mul_pos ‹0 < n› ‹0 < t›
          nlinarith
    · -- Negative square branch contradicts `0 < Q`.
      exfalso
      have : Q X Y Z ≤ 0 := by rw [ht0]; exact neg_nonpos.mpr (sq_nonneg t0)
      nlinarith
  · -- Negative square branch contradicts `0 < P/3`.
    exfalso
    have hPdivpos : 0 < P X Y Z / 3 := by
      -- `P = 3*(P/3)` and `0<P`.
      sorry
    have : P X Y Z / 3 ≤ 0 := by rw [hn0]; exact neg_nonpos.mpr (sq_nonneg n0)
    nlinarith
```

Finally convert `n,t` to `m,n` by `t = 2*m - n`. Since both `n` and `t` are odd, `(t+n)/2` is an integer and is the desired `m`.

```lean
lemma odd_second_param_nonunit
    {X Y Z : ℤ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hcop : Int.gcd X Y = 1) (hYodd : Odd Y)
    (hE : EisensteinTriple X Y Z)
    (hnotunit : ¬ (X = 1 ∧ Y = 1 ∧ Z = 1)) :
    ∃ m n : ℤ, 0 < n ∧ n < m ∧ Int.gcd m n = 1 ∧ ¬ (3 : ℤ) ∣ m + n ∧
      (Z = m ^ 2 - m * n + n ^ 2 ∧
       X = m ^ 2 - n ^ 2 ∧ Y = 2 * m * n - n ^ 2) := by
  obtain ⟨n, t, hnpos, htpos, hnodd, htodd, hntcop, hP, hQ, hYnt⟩ :=
    square_extraction_odd_second hX hY hZ hcop hYodd hE hnotunit
  have htn_even : Even (t + n) := htodd.add_odd hnodd
  let m : ℤ := (t + n) / 2
  have hm_def : 2 * m = t + n := by
    -- `htn_even` and `Int.ediv_mul_cancel`.
    rcases htn_even with ⟨k, hk⟩
    change 2 * ((t + n) / 2) = t + n
    rw [hk]
    ring
  have ht_eq : t = 2 * m - n := by nlinarith

  have hY_formula : Y = 2 * m * n - n ^ 2 := by
    rw [hYnt, ht_eq]
    ring
  have hX_formula : X = m ^ 2 - n ^ 2 := by
    -- Subtract `P = 3*n^2` from `Q = t^2`:
    -- `4*X - 2*Y = t^2 - 3*n^2`, then use `Y=n*t` and `t=2*m-n`.
    unfold P Q at hP hQ
    nlinarith [hY_formula]
  have hZ_formula : Z = m ^ 2 - m * n + n ^ 2 := by
    -- Add `P = 3*n^2` and `Q = t^2`:
    -- `4*Z = t^2 + 3*n^2`, then use `t=2*m-n`.
    unfold P Q at hP hQ
    nlinarith
  have hmn_coprime : Int.gcd m n = 1 := by
    -- Since `t = 2*m-n`, `gcd n t = gcd n (2*m)`.
    -- Also `n` is odd, so `gcd n 2 = 1`; conclude from `hntcop`.
    -- Useful APIs: `Int.gcd_add_mul_left_left/right`, `Int.isCoprime_two_left/right`,
    -- `Int.isCoprime_iff_gcd_eq_one`.
    sorry
  have hmn_gt : n < m := by
    -- From `X = m^2 - n^2` and `0 < X`, with `0 < n` and `0 < m`.
    -- A simpler route: prove `n < t` from `X = (t^2 - n^2)/4`, then `2*m=t+n`.
    sorry
  have h3 : ¬ (3 : ℤ) ∣ m + n := by
    -- If `3 ∣ m+n`, then `3 ∣ t = 2*m-n`; hence `3 ∣ Q = t^2`.
    -- This contradicts the coprime/extraction lemma, since `P = 3*n^2` is the only factor carrying 3.
    sorry
  exact ⟨m, n, hnpos, hmn_gt, hmn_coprime, h3,
    hZ_formula, hX_formula, hY_formula⟩
```

## Final corrected theorem

```lean
theorem eisensteinTriple_primitive_param_or_unit
    {X Y Z : ℤ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hcop : Int.gcd X Y = 1)
    (hE : EisensteinTriple X Y Z) :
    (X = 1 ∧ Y = 1 ∧ Z = 1) ∨
      ∃ m n : ℤ, 0 < n ∧ n < m ∧ Int.gcd m n = 1 ∧ ¬ (3 : ℤ) ∣ m + n ∧
        EisensteinParam X Y Z m n := by
  by_cases hXY : X = Y
  · left
    exact EisensteinTriple.unit_of_eq hX hZ hcop hE hXY
  · right
    -- Primitive parity split. If both were even, gcd would not be 1.
    -- If both are odd, that is allowed; choose the `Y`-odd branch.
    rcases Int.even_or_odd Y with hYeven | hYodd
    · have hXodd : Odd X := by
        by_contra hXnotodd
        have hXeven : Even X := Int.not_odd_iff_even.mp hXnotodd
        -- `2 ∣ X` and `2 ∣ Y` contradict `Int.gcd X Y = 1`.
        have hbad : 2 ∣ (Int.gcd X Y : ℤ) :=
          Int.dvd_coe_gcd hXeven.two_dvd hYeven.two_dvd
        rw [hcop] at hbad
        norm_num at hbad
      obtain ⟨m, n, hn, hnm, hmn, h3, hZ, hY_formula, hX_formula⟩ :=
        odd_second_param_nonunit hY hX hZ (by simpa [Int.gcd_comm] using hcop)
          hXodd hE.symm ?_
      · exact ⟨m, n, hn, hnm, hmn, h3,
          ⟨hZ, Or.inr ⟨hY_formula, hX_formula⟩⟩⟩
      · intro hunit_swapped
        exact hXY hunit_swapped.2.1.symm.trans hunit_swapped.1
    · obtain ⟨m, n, hn, hnm, hmn, h3, hZ, hX_formula, hY_formula⟩ :=
        odd_second_param_nonunit hX hY hZ hcop hYodd hE ?_
      · exact ⟨m, n, hn, hnm, hmn, h3,
          ⟨hZ, Or.inl ⟨hX_formula, hY_formula⟩⟩⟩
      · intro hunit
        exact hXY hunit.1.trans hunit.2.1.symm

/-- Original theorem with the needed non-unit hypothesis. -/
theorem eisensteinTriple_primitive_param_of_ne
    {X Y Z : ℤ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hcop : Int.gcd X Y = 1) (hXY : X ≠ Y)
    (hE : EisensteinTriple X Y Z) :
    ∃ m n : ℤ, 0 < n ∧ n < m ∧ Int.gcd m n = 1 ∧ ¬ (3 : ℤ) ∣ m + n ∧
      EisensteinParam X Y Z m n := by
  rcases eisensteinTriple_primitive_param_or_unit hX hY hZ hcop hE with hunit | hparam
  · exact (hXY (hunit.1.trans hunit.2.1.symm)).elim
  · exact hparam

end MazurProof.QuarticEisenstein
```

## Practical implementation order

1. Add `EisensteinParam.triple`, `EisensteinTriple.symm`, and `EisensteinParam.symm`.
2. Add `EisensteinTriple.unit_of_eq`; this fixes the false original theorem.
3. Prove the algebraic factor identity and positivity of `P,Q`.
4. Prove the mod-3 sign lemma `three_dvd_P_of_primitive_odd_second_nonunit`.
5. Prove `coprime_P_div3_Q_of_primitive_odd_second` by prime-divisor contradiction.
6. Use `Int.sq_of_gcd_eq_one` in `square_extraction_odd_second`.
7. Convert `n,t` to `m,n` using `m=(t+n)/2` in `odd_second_param_nonunit`.
8. Finish by parity-splitting on `Y`; if `Y` is even, apply the odd-second theorem to `(Y,X,Z)` and wrap with the swapped branch of `EisensteinParam`.
