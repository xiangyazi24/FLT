# Q2731: primitive positive Eisenstein triples by rational slope

Target: `FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean`.

## Verdict

The stated residual is **correct as written**. In fact, no swap is needed if the canonical slope is chosen as

```lean
q = (Y : ℚ) / (Z + X : ℤ)
```

for a positive primitive triple

```lean
Z ^ 2 = X ^ 2 - X * Y + Y ^ 2.
```

The pair `(m,n)` is the reduced numerator/denominator of `q`:

```lean
n = q.num
m = q.den
```

with `q.den` coerced to `ℤ`. Then `0 < n`, `n < m`, and `IsCoprime m n`. The slope derivation gives exactly one of the two sectors:

```lean
¬ (3 : ℤ) ∣ m + n
  -> X = m^2 - n^2
  -> Y = 2*m*n - n^2
  -> Z = m^2 - m*n + n^2

(3 : ℤ) ∣ m + n
  -> 3*X = m^2 - n^2
  -> 3*Y = 2*m*n - n^2
  -> 3*Z = m^2 - m*n + n^2
```

The second orientation in `EisensteinParam`/`EisensteinFullParam` is still useful for symmetry, but the slope `Y/(Z+X)` always lands in the first orientation.

There are no missing positive primitive exceptional triples besides the unit sector `(1,1,1)`. Note that `(1,1,1)` is also parametrized by the divided sector with `(m,n)=(2,1)`; the explicit unit disjunct is harmless and convenient for descent.

Small examples:

```text
m=2,n=1, 3 | m+n:  (X,Y,Z) = (1,1,1)
m=3,n=1, ¬3|m+n:  (X,Y,Z) = (8,5,7)
m=3,n=2, ¬3|m+n:  (X,Y,Z) = (5,8,7)
m=5,n=1, 3 | m+n:  (X,Y,Z) = (8,3,7)
```

All are positive and primitive, and each satisfies `Z^2 = X^2 - X*Y + Y^2`.

## Imports

```lean
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Rat.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic
```

Useful APIs to grep or `#check`:

```lean
#check Rat.num_pos
#check Rat.num_lt_denom_iff
#check Rat.pos
#check Rat.den_nz
#check Rat.num_div_den      -- used by Mathlib/NumberTheory/PythagoreanTriples in many checkouts
#check Rat.num_divInt_den   -- newer/alternate name in some checkouts
#check Rat.reduced
#check Int.isCoprime_iff_gcd_eq_one
#check IsCoprime.dvd_of_dvd_mul_left
#check IsCoprime.dvd_of_dvd_mul_right
#check Int.ModEq
#check Int.modEq_iff_dvd
#check Int.emod_two_eq_zero_or_one
```

## Definitions

```lean
namespace MazurProof.QuarticEisenstein

def EisensteinTriple (X Y Z : ℤ) : Prop :=
  Z ^ 2 = X ^ 2 - X * Y + Y ^ 2

def EisensteinParam (X Y Z m n : ℤ) : Prop :=
  Z = m ^ 2 - m * n + n ^ 2 ∧
  ((X = m ^ 2 - n ^ 2 ∧ Y = 2 * m * n - n ^ 2) ∨
   (Y = m ^ 2 - n ^ 2 ∧ X = 2 * m * n - n ^ 2))

def EisensteinFullParam (X Y Z m n : ℤ) : Prop :=
  0 < n ∧ n < m ∧ IsCoprime m n ∧
  ((¬ (3 : ℤ) ∣ m + n ∧ EisensteinParam X Y Z m n) ∨
    ((3 : ℤ) ∣ m + n ∧
      3 * Z = m ^ 2 - m * n + n ^ 2 ∧
      ((3 * X = m ^ 2 - n ^ 2 ∧ 3 * Y = 2 * m * n - n ^ 2) ∨
       (3 * Y = m ^ 2 - n ^ 2 ∧ 3 * X = 2 * m * n - n ^ 2))))
```

## Basic algebra identities

These should be the first lemmas in the file. They keep the later proof linear.

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

lemma eisenstein_raw_identity (m n : ℤ) :
    (m ^ 2 - m * n + n ^ 2) ^ 2 =
      (m ^ 2 - n ^ 2) ^ 2 -
        (m ^ 2 - n ^ 2) * (2 * m * n - n ^ 2) +
        (2 * m * n - n ^ 2) ^ 2 := by
  ring

lemma eisenstein_divided_identity (m n : ℤ) :
    (m ^ 2 - m * n + n ^ 2) ^ 2 =
      (m ^ 2 - n ^ 2) ^ 2 -
        (m ^ 2 - n ^ 2) * (2 * m * n - n ^ 2) +
        (2 * m * n - n ^ 2) ^ 2 := by
  ring
```

The divided identity is the same polynomial identity; in use, multiply the target equation by `9` and rewrite with `3*X`, `3*Y`, `3*Z`.

## Positivity and unit exception

The slope denominator `Z+X` is positive, and the slope is strictly between `0` and `1`.

```lean
lemma eisenstein_Z_pos_den {X Y Z : ℤ}
    (hX : 0 < X) (hZ : 0 < Z) : 0 < Z + X := by
  nlinarith

lemma eisenstein_Y_lt_Z_add_X {X Y Z : ℤ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hE : EisensteinTriple X Y Z) : Y < Z + X := by
  have hsq : Z ^ 2 - (Y - X) ^ 2 = X * Y := by
    unfold EisensteinTriple at hE
    nlinarith
  have hpos : 0 < Z ^ 2 - (Y - X) ^ 2 := by
    nlinarith [mul_pos hX hY]
  -- From `Z^2 > (Y-X)^2` and `0<Z`, conclude `Y-X < Z`.
  -- `nlinarith` can finish after splitting on `Y-X ≤ 0` or using `sq_lt_sq`.
  have hYXlt : Y - X < Z := by
    -- robust approach:
    --   have habs : |Y-X| < Z := abs_lt_of_sq_lt_sq ... (le_of_lt hZ)
    --   exact lt_of_le_of_lt (le_abs_self _) habs
    sorry
  nlinarith

lemma eisenstein_slope_pos_lt_one {X Y Z : ℤ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hE : EisensteinTriple X Y Z) :
    0 < (Y : ℚ) / (Z + X : ℤ) ∧ (Y : ℚ) / (Z + X : ℤ) < 1 := by
  have hdenZ : (0 : ℤ) < Z + X := eisenstein_Z_pos_den hX hZ
  have hylt : Y < Z + X := eisenstein_Y_lt_Z_add_X hX hY hZ hE
  constructor
  · positivity
  · rw [div_lt_one]
    · exact_mod_cast hylt
    · exact_mod_cast hdenZ
```

Unit is the only equality case `X=Y`:

```lean
lemma EisensteinTriple.unit_of_eq {X Y Z : ℤ}
    (hX : 0 < X) (hZ : 0 < Z)
    (hcop : IsCoprime X Y) (hE : EisensteinTriple X Y Z)
    (hXY : X = Y) : X = 1 ∧ Y = 1 ∧ Z = 1 := by
  subst Y
  unfold EisensteinTriple at hE
  have hZsq : Z ^ 2 = X ^ 2 := by nlinarith
  have hZX : Z = X := by
    rcases eq_or_eq_neg_of_sq_eq_sq Z X hZsq with h | h
    · exact h
    · nlinarith
  subst Z
  have hcopXX : IsCoprime X X := hcop
  rcases hcopXX with ⟨a, b, hab⟩
  have hunit : X ∣ (1 : ℤ) := by
    refine ⟨a + b, ?_⟩
    nlinarith
  have hXle1 : X ≤ 1 := by
    exact Int.le_of_dvd (by norm_num) hunit
  have hX1 : X = 1 := by nlinarith
  exact ⟨hX1, hX1, hX1⟩
```

## Canonical reduced pair `(m,n)`

Use the reduced rational slope.

```lean
noncomputable def eisensteinSlope (X Y Z : ℤ) : ℚ :=
  (Y : ℚ) / (Z + X : ℤ)

noncomputable def eisenstein_m (X Y Z : ℤ) : ℤ :=
  ((eisensteinSlope X Y Z).den : ℤ)

noncomputable def eisenstein_n (X Y Z : ℤ) : ℤ :=
  (eisensteinSlope X Y Z).num

lemma eisenstein_mn_pos_coprime {X Y Z : ℤ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hE : EisensteinTriple X Y Z) :
    0 < eisenstein_n X Y Z ∧
      eisenstein_n X Y Z < eisenstein_m X Y Z ∧
      IsCoprime (eisenstein_m X Y Z) (eisenstein_n X Y Z) := by
  let q := eisensteinSlope X Y Z
  have hq : 0 < q ∧ q < 1 := eisenstein_slope_pos_lt_one hX hY hZ hE
  have hnpos : 0 < q.num := by
    simpa [q] using (Rat.num_pos.mp hq.1)
  have hnltm : q.num < (q.den : ℤ) := by
    simpa [q] using (Rat.num_lt_denom_iff.mpr hq.2)
  have hcop_gcd : Int.gcd (q.den : ℤ) q.num = 1 := by
    rw [Int.gcd_comm]
    exact q.reduced
  exact ⟨by simpa [eisenstein_n, q], by simpa [eisenstein_m, eisenstein_n, q],
    Int.isCoprime_iff_gcd_eq_one.mpr hcop_gcd⟩
```

If your checkout names the rational reconstruction lemma differently, use whichever one compiles:

```lean
-- older Mathlib/PythagoreanTriples style:
have hq_num_den : q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm

-- newer style often available:
have hq_num_den : q = q.num /. (q.den : ℤ) := (Rat.num_divInt_den q).symm
```

## From slope to an integer scale

The key slope equation is

```lean
m * Y = n * (Z + X)
```

for the reduced pair. Since `IsCoprime m n`, this gives a common scale `t`.

```lean
lemma exists_scale_of_reduced_slope
    {X Y Z m n : ℤ}
    (hmn : IsCoprime m n)
    (hcross : m * Y = n * (Z + X)) :
    ∃ t : ℤ, Y = n * t ∧ Z + X = m * t := by
  have hm_dvd : m ∣ Z + X := by
    apply hmn.dvd_of_dvd_mul_right
    refine ⟨Y, ?_⟩
    nlinarith
  rcases hm_dvd with ⟨t, hW⟩
  refine ⟨t, ?_, hW⟩
  have hnmt : n * (m * t) = m * Y := by nlinarith
  have hm_ne_zero : m ≠ 0 := by
    intro hm0
    subst m
    -- In use `0<n<m`, so this cannot happen. If this lemma is used standalone,
    -- pass `m ≠ 0` as an extra hypothesis.
    sorry
  apply (mul_left_inj' hm_ne_zero).mp
  nlinarith
```

For a standalone compile-ready version, include `hm_ne_zero : m ≠ 0` as an explicit hypothesis. In the main theorem it follows from `0 < n ∧ n < m`.

Now the scale equations are pure algebra.

```lean
private def D (m n : ℤ) : ℤ := m ^ 2 - m * n + n ^ 2
private def R (m n : ℤ) : ℤ := 2 * m - n
private def U (m n : ℤ) : ℤ := m ^ 2 - n ^ 2
private def V (m n : ℤ) : ℤ := 2 * m * n - n ^ 2

lemma scale_equations_of_slope
    {X Y Z m n t : ℤ}
    (hE : EisensteinTriple X Y Z)
    (hY : Y = n * t) (hW : Z + X = m * t) :
    R m n * Z = D m n * t ∧
      R m n * X = U m n * t ∧
      R m n * Y = V m n * t := by
  have hZ : X = m * t - Z := by nlinarith
  subst Y
  unfold EisensteinTriple at hE
  unfold D R U V
  constructor
  · nlinarith
  constructor
  · nlinarith
  · ring
```

## The exact `3` split

This is the arithmetic heart. It is elementary, and these are the exact lemmas to prove.

```lean
lemma D_R_gcd_dvd_three {m n : ℤ}
    (hmn : IsCoprime m n) :
    (Int.gcd (D m n) (R m n) : ℤ) ∣ 3 := by
  -- A common divisor of `D` and `R=2m-n` divides
  --   4*D - R^2 = 3*n^2.
  -- It also divides `R` and is coprime to `n`, because any common divisor of `R` and `n`
  -- divides `2m` and `n`; coprimality of `m,n` leaves only possibly `2`, but `D` is odd
  -- in that subcase. The clean prime-divisor proof is easiest.
  sorry

lemma three_dvd_D_and_R_iff {m n : ℤ}
    (hmn : IsCoprime m n) :
    (3 : ℤ) ∣ D m n ∧ (3 : ℤ) ∣ R m n ↔ (3 : ℤ) ∣ m + n := by
  unfold D R
  constructor
  · rintro ⟨hD, hR⟩
    -- From `R=2m-n ≡ 0`, get `n ≡ 2m`; then `m+n ≡ 3m ≡ 0`.
    -- Use `Int.ModEq` or direct divisibility algebra.
    sorry
  · intro hsum
    constructor
    · -- If `n ≡ -m`, then `D ≡ 3*m^2`.
      sorry
    · -- If `n ≡ -m`, then `R=2m-n ≡ 3m`.
      sorry

lemma D_R_gcd_eq_one_or_three {m n : ℤ}
    (hmn : IsCoprime m n) :
    ((¬ (3 : ℤ) ∣ m + n) → Int.gcd (D m n) (R m n) = 1) ∧
    (((3 : ℤ) ∣ m + n) → Int.gcd (D m n) (R m n) = 3) := by
  constructor
  · intro hnot
    have hdvd : (Int.gcd (D m n) (R m n) : ℤ) ∣ 3 := D_R_gcd_dvd_three hmn
    -- `Int.gcd` is nonnegative. Since it divides prime `3`, it is `1` or `3`.
    -- Rule out `3` using `three_dvd_D_and_R_iff` and `hnot`.
    sorry
  · intro h3
    -- Show 3 divides both, so 3 divides the gcd; `D_R_gcd_dvd_three` gives the reverse.
    sorry
```

The raw coordinate gcd is the same split.

```lean
lemma U_V_common_gcd_split {m n : ℤ}
    (hmn : IsCoprime m n) :
    ((¬ (3 : ℤ) ∣ m + n) → IsCoprime (U m n) (V m n)) ∧
    (((3 : ℤ) ∣ m + n) →
      (3 : ℤ) ∣ U m n ∧ (3 : ℤ) ∣ V m n ∧
      IsCoprime (U m n / 3) (V m n / 3)) := by
  -- Prime-divisor proof.
  -- If p divides `n` and `U=m^2-n^2`, then p divides m, contradiction.
  -- If p divides `R=2m-n` and `U`, then p divides 3.
  -- Thus the only possible common prime is 3, exactly when `m+n` is divisible by 3.
  sorry
```

This is also the lemma that proves “denominators create the `3 | m+n` sector”: the only possible loss of primitivity in `(U,V,D)` is a common factor `3`, and it occurs exactly when `3 ∣ m+n`.

## Scale collapses to raw or divided sector

This theorem is the main bridge from the slope calculation to `EisensteinFullParam`.

```lean
lemma primitive_scale_is_one_or_three
    {X Y Z m n t : ℤ}
    (hX : 0 < X) (hYpos : 0 < Y) (hZ : 0 < Z)
    (hprim : IsCoprime X Y)
    (hmn : IsCoprime m n)
    (hnpos : 0 < n) (hnm : n < m)
    (hY : Y = n * t) (hW : Z + X = m * t)
    (hE : EisensteinTriple X Y Z) :
    ((¬ (3 : ℤ) ∣ m + n) →
      X = U m n ∧ Y = V m n ∧ Z = D m n) ∧
    (((3 : ℤ) ∣ m + n) →
      3 * X = U m n ∧ 3 * Y = V m n ∧ 3 * Z = D m n) := by
  have hrpos : 0 < R m n := by
    unfold R
    nlinarith
  obtain ⟨hRZ, hRX, hRY⟩ := scale_equations_of_slope hE hY hW
  have hsplit := D_R_gcd_eq_one_or_three hmn
  have huvsplit := U_V_common_gcd_split hmn
  constructor
  · intro hnot3
    have hg : Int.gcd (D m n) (R m n) = 1 := hsplit.1 hnot3
    -- From `R*Z=D*t` and gcd(D,R)=1, get `R ∣ t`; write `t=R*k`.
    -- Then `Z=D*k`, `X=U*k`, `Y=V*k`.
    -- Since `IsCoprime X Y` and `IsCoprime U V`, force `k=1` using positivity.
    sorry
  · intro h3
    have hg : Int.gcd (D m n) (R m n) = 3 := hsplit.2 h3
    -- Write `D=3*D0`, `R=3*R0`, use coprime(D0,R0), then `t=R0*k`.
    -- Get `3*Z=D*k`, `3*X=U*k`, `3*Y=V*k`.
    -- Since `IsCoprime X Y` and `IsCoprime (U/3) (V/3)`, force `k=1`.
    sorry
```

## Final parametrization theorem

The final proof is then short.

```lean
theorem eisensteinTriplePrimitiveParamOrUnit_by_slope :
    EisensteinTriplePrimitiveParamOrUnit := by
  intro X Y Z hX hY hZ hprim hE
  by_cases hXY : X = Y
  · left
    exact EisensteinTriple.unit_of_eq hX hZ hprim hE hXY
  · right
    let q : ℚ := eisensteinSlope X Y Z
    let m : ℤ := eisenstein_m X Y Z
    let n : ℤ := eisenstein_n X Y Z
    have hmn_pos : 0 < n ∧ n < m ∧ IsCoprime m n := by
      simpa [m, n] using eisenstein_mn_pos_coprime hX hY hZ hE
    rcases hmn_pos with ⟨hnpos, hnltm, hmn⟩

    have hqeq : (Y : ℚ) / (Z + X : ℤ) = (n : ℚ) / (m : ℚ) := by
      -- unfold `m,n,q`; use `Rat.num_div_den` or `Rat.num_divInt_den`.
      sorry
    have hcross : m * Y = n * (Z + X) := by
      -- Cross multiply `hqeq`; denominator nonzero from `0 < m` and `0 < Z+X`.
      sorry
    obtain ⟨t, hYscale, hWscale⟩ := exists_scale_of_reduced_slope hmn hcross

    obtain ⟨hraw, hdiv⟩ :=
      primitive_scale_is_one_or_three hX hY hZ hprim hmn hnpos hnltm
        hYscale hWscale hE

    by_cases h3 : (3 : ℤ) ∣ m + n
    · obtain ⟨hX3, hY3, hZ3⟩ := hdiv h3
      refine ⟨m, n, hnpos, hnltm, hmn, Or.inr ?_⟩
      refine ⟨h3, hZ3, Or.inl ⟨hX3, hY3⟩⟩
    · obtain ⟨hXraw, hYraw, hZraw⟩ := hraw h3
      refine ⟨m, n, hnpos, hnltm, hmn, Or.inl ?_⟩
      refine ⟨h3, hZraw, Or.inl ⟨hXraw, hYraw⟩⟩
```

The `hXY` split is only used to return the explicit unit disjunct. If you prefer, you can remove the split and always return the existential; `(1,1,1)` will go to the divided sector with `(m,n)=(2,1)`.

## Concrete divisibility proof notes

The most important prime-divisor facts can be proved with these identities:

```lean
example (m n : ℤ) :
    4 * D m n - R m n ^ 2 = 3 * n ^ 2 := by
  unfold D R
  ring

example (m n : ℤ) :
    U m n = (m - n) * (m + n) := by
  unfold U
  ring

example (m n : ℤ) :
    V m n = n * R m n := by
  unfold V R
  ring

example (m n : ℤ) :
    (3 : ℤ) ∣ m + n → (3 : ℤ) ∣ U m n := by
  intro h
  unfold U
  -- `m^2-n^2=(m-n)(m+n)`.
  exact h.mul_left (m - n)

example (m n : ℤ) :
    (3 : ℤ) ∣ m + n → (3 : ℤ) ∣ V m n := by
  intro h
  unfold V
  -- Since `2*m*n-n^2 = n*(2*m-n)` and `2*m-n = 2*(m+n)-3*n`.
  rcases h with ⟨k, hk⟩
  refine ⟨n * (2 * k - n), ?_⟩
  nlinarith

example (m n : ℤ) :
    (3 : ℤ) ∣ m + n → (3 : ℤ) ∣ D m n := by
  intro h
  rcases h with ⟨k, hk⟩
  unfold D
  refine ⟨m ^ 2 - m * k + k ^ 2, ?_⟩
  nlinarith
```

For the converse, use `Int.ModEq`:

```lean
-- If `3 ∣ R m n`, then `n ≡ 2*m [ZMOD 3]`.
-- Substitute into `D ≡ 0`; it becomes `3*m^2 ≡ 0`, hence no extra condition.
-- Directly, `m+n = 3*m - R`, so `3 ∣ R -> 3 ∣ m+n`.
example (m n : ℤ) (hR : (3 : ℤ) ∣ R m n) : (3 : ℤ) ∣ m + n := by
  unfold R at hR
  rcases hR with ⟨k, hk⟩
  refine ⟨m - k, ?_⟩
  nlinarith
```

This last identity is very useful: for the `D,R` gcd, once a common divisor is forced to be `3`, divisibility of `R` alone gives `3 ∣ m+n`.

## Summary for implementation order

1. Add the raw polynomial identity and symmetry lemmas.
2. Prove `eisenstein_Y_lt_Z_add_X`; this establishes `0 < q < 1`.
3. Define `eisensteinSlope`, `eisenstein_m`, `eisenstein_n`; prove `0<n<m` and `IsCoprime m n` from `Rat.reduced`.
4. Prove `exists_scale_of_reduced_slope` from cross multiplication and coprimality.
5. Prove `scale_equations_of_slope` by `ring`/`nlinarith`.
6. Prove the arithmetic split:
   * `D_R_gcd_dvd_three`
   * `three_dvd_D_and_R_iff`
   * `D_R_gcd_eq_one_or_three`
   * `U_V_common_gcd_split`
7. Prove `primitive_scale_is_one_or_three` to collapse the scale to raw or divided formulas.
8. Finish `eisensteinTriplePrimitiveParamOrUnit_by_slope` by a `by_cases h3 : (3:ℤ) ∣ m+n` split.

end MazurProof.QuarticEisenstein
```