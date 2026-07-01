# Q2803 dm-codex2: proof plan for `CommonDenomSquareclassRepsToPrimitiveCoverIntStatement`

Namespace: `MazurProof.RationalPointsN12`.

Target file: `FLT/Assumptions/MazurProof/N12E1FullCoverExtraction.lean`.

I could not inspect the local worktree file through the GitHub connector; the plan below is based on the definitions in the prompt.

## 1. Truth value of the statement

The statement is mathematically true as written, assuming the displayed definitions are exactly the active local definitions.

Given

```lean
X = (d0 : ℚ) * r0 ^ 2
X - 1 = (d1 : ℚ) * r1 ^ 2
X + 3 = (d3 : ℚ) * r3 ^ 2
E1FullCoverCurve X Y
Y ≠ 0
r0 ≠ 0, r1 ≠ 0, r3 ≠ 0
```

the cover equations follow after choosing a common nonzero integer denominator `T` with

```lean
r0 = (A : ℚ) / (T : ℚ)
r1 = (B : ℚ) / (T : ℚ)
r3 = (C : ℚ) / (T : ℚ)
```

Then subtracting the squareclass equations gives

```lean
d0 * A ^ 2 - d1 * B ^ 2 = T ^ 2
d3 * C ^ 2 - d0 * A ^ 2 = 3 * T ^ 2
```

A four-variable gcd normalization makes `(A,B,C,T)` primitive, and homogeneity preserves the cover equations. Nonzero-ness of `A,B,C,T` survives because `r0,r1,r3` and the common denominator are nonzero.

`ProductSquareclassCondition d0 d1 d3` follows from the curve equation:

```lean
Y ^ 2 = X * (X - 1) * (X + 3)
      = ((d0*d1*d3 : ℤ) : ℚ) * (r0*r1*r3)^2
```

so

```lean
((d0*d1*d3 : ℤ) : ℚ) = (Y / (r0*r1*r3))^2
```

with nonzero witness because `Y`, `r0`, `r1`, `r3` are nonzero.

No extra hypothesis is missing.

## 2. Minimal lemma DAG

Keep these helpers local to `N12E1FullCoverExtraction.lean` or move only the generic gcd/rat-denominator helpers to a small utility file if multiple N=12 files need them.

### DAG overview

| order | lemma | purpose |
|---:|---|---|
| 1 | `productSquareclassCondition_of_curve_squareclasses` | prove `ProductSquareclassCondition d0 d1 d3` from curve + three squareclass reps |
| 2 | `rat_common_den3` | construct integer `A0 B0 C0 T0` for three nonzero rationals with common denominator |
| 3 | `rawCoverInt_of_common_den_squareclasses` | prove raw `CoverInt d0 d1 d3 A0 B0 C0 T0` |
| 4 | `gcd4` + API lemmas | common divisor/greatest common divisor of four integers |
| 5 | `primitive_div_gcd4_data` | divide by `gcd4` to obtain primitive nonzero data and equalities `A0=g*A`, etc. |
| 6 | `coverInt_div_common_factor` | homogeneous cover equations descend after common division |
| 7 | `primitiveCoverInt_of_rawCoverInt` | package normalized primitive cover data |
| 8 | final residual theorem | assemble `E1FullCoverIntData X Y` |

### Exact target signatures

```lean
namespace MazurProof.RationalPointsN12

private theorem productSquareclassCondition_of_curve_squareclasses
    {X Y : ℚ} {d0 d1 d3 : ℤ} {r0 r1 r3 : ℚ}
    (hE : E1FullCoverCurve X Y) (hY : Y ≠ 0)
    (hr0nz : r0 ≠ 0) (hr1nz : r1 ≠ 0) (hr3nz : r3 ≠ 0)
    (h0 : X = (d0 : ℚ) * r0 ^ 2)
    (h1 : X - 1 = (d1 : ℚ) * r1 ^ 2)
    (h3 : X + 3 = (d3 : ℚ) * r3 ^ 2) :
    ProductSquareclassCondition d0 d1 d3

private theorem rat_common_den3
    {r0 r1 r3 : ℚ}
    (hr0nz : r0 ≠ 0) (hr1nz : r1 ≠ 0) (hr3nz : r3 ≠ 0) :
    ∃ A0 B0 C0 T0 : ℤ,
      T0 ≠ 0 ∧ A0 ≠ 0 ∧ B0 ≠ 0 ∧ C0 ≠ 0 ∧
      r0 = (A0 : ℚ) / (T0 : ℚ) ∧
      r1 = (B0 : ℚ) / (T0 : ℚ) ∧
      r3 = (C0 : ℚ) / (T0 : ℚ)

private theorem rawCoverInt_of_common_den_squareclasses
    {X : ℚ} {d0 d1 d3 A0 B0 C0 T0 : ℤ}
    (hT0 : T0 ≠ 0)
    (hr0 : X = (d0 : ℚ) * (((A0 : ℚ) / (T0 : ℚ)) ^ 2))
    (hr1 : X - 1 = (d1 : ℚ) * (((B0 : ℚ) / (T0 : ℚ)) ^ 2))
    (hr3 : X + 3 = (d3 : ℚ) * (((C0 : ℚ) / (T0 : ℚ)) ^ 2)) :
    CoverInt d0 d1 d3 A0 B0 C0 T0

private def gcd4 (A B C T : ℤ) : ℕ :=
  Nat.gcd (Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs) T.natAbs

private theorem gcd4_pos_of_T_ne_zero
    {A B C T : ℤ} (hT : T ≠ 0) : 0 < gcd4 A B C T

private theorem gcd4_dvd_A {A B C T : ℤ} :
    ((gcd4 A B C T : ℕ) : ℤ) ∣ A
private theorem gcd4_dvd_B {A B C T : ℤ} :
    ((gcd4 A B C T : ℕ) : ℤ) ∣ B
private theorem gcd4_dvd_C {A B C T : ℤ} :
    ((gcd4 A B C T : ℕ) : ℤ) ∣ C
private theorem gcd4_dvd_T {A B C T : ℤ} :
    ((gcd4 A B C T : ℕ) : ℤ) ∣ T

private theorem common_dvd_gcd4
    {A B C T d : ℤ}
    (hdA : d ∣ A) (hdB : d ∣ B) (hdC : d ∣ C) (hdT : d ∣ T) :
    d ∣ ((gcd4 A B C T : ℕ) : ℤ)

private theorem primitive_div_gcd4_data
    {A0 B0 C0 T0 : ℤ}
    (hT0 : T0 ≠ 0) :
    ∃ A B C T : ℤ,
      T ≠ 0 ∧
      (A0 ≠ 0 → A ≠ 0) ∧
      (B0 ≠ 0 → B ≠ 0) ∧
      (C0 ≠ 0 → C ≠ 0) ∧
      PrimitiveInt4 A B C T ∧
      A0 = ((gcd4 A0 B0 C0 T0 : ℕ) : ℤ) * A ∧
      B0 = ((gcd4 A0 B0 C0 T0 : ℕ) : ℤ) * B ∧
      C0 = ((gcd4 A0 B0 C0 T0 : ℕ) : ℤ) * C ∧
      T0 = ((gcd4 A0 B0 C0 T0 : ℕ) : ℤ) * T

private theorem coverInt_div_common_factor
    {d0 d1 d3 A0 B0 C0 T0 A B C T g : ℤ}
    (hg : g ≠ 0)
    (hA : A0 = g * A) (hB : B0 = g * B)
    (hC : C0 = g * C) (hT : T0 = g * T)
    (hcover : CoverInt d0 d1 d3 A0 B0 C0 T0) :
    CoverInt d0 d1 d3 A B C T

private theorem primitiveCoverInt_of_rawCoverInt
    {d0 d1 d3 A0 B0 C0 T0 : ℤ}
    (hT0 : T0 ≠ 0) (hA0 : A0 ≠ 0) (hB0 : B0 ≠ 0) (hC0 : C0 ≠ 0)
    (hcover0 : CoverInt d0 d1 d3 A0 B0 C0 T0) :
    ∃ A B C T : ℤ,
      T ≠ 0 ∧ A ≠ 0 ∧ B ≠ 0 ∧ C ≠ 0 ∧
      PrimitiveInt4 A B C T ∧
      (A0 : ℚ) / (T0 : ℚ) = (A : ℚ) / (T : ℚ) ∧
      (B0 : ℚ) / (T0 : ℚ) = (B : ℚ) / (T : ℚ) ∧
      (C0 : ℚ) / (T0 : ℚ) = (C : ℚ) / (T : ℚ) ∧
      CoverInt d0 d1 d3 A B C T

end MazurProof.RationalPointsN12
```

## 3. Hard lemma proof skeletons and API hints

### 3.1 Product squareclass condition

Proof idea: use witness `Y / (r0*r1*r3)`.

```lean
private theorem productSquareclassCondition_of_curve_squareclasses
    {X Y : ℚ} {d0 d1 d3 : ℤ} {r0 r1 r3 : ℚ}
    (hE : E1FullCoverCurve X Y) (hY : Y ≠ 0)
    (hr0nz : r0 ≠ 0) (hr1nz : r1 ≠ 0) (hr3nz : r3 ≠ 0)
    (h0 : X = (d0 : ℚ) * r0 ^ 2)
    (h1 : X - 1 = (d1 : ℚ) * r1 ^ 2)
    (h3 : X + 3 = (d3 : ℚ) * r3 ^ 2) :
    ProductSquareclassCondition d0 d1 d3 := by
  refine ⟨Y / (r0 * r1 * r3), ?_, ?_⟩
  · field_simp [hY, hr0nz, hr1nz, hr3nz]
  · have hcurve : Y ^ 2 = X * (X - 1) * (X + 3) := by
      simpa [E1FullCoverCurve] using hE
    calc
      (((d0 * d1 * d3 : ℤ) : ℚ))
          = Y ^ 2 / (r0 * r1 * r3) ^ 2 := by
              field_simp [hr0nz, hr1nz, hr3nz]
              rw [hcurve, h0, h1, h3]
              ring
      _ = (Y / (r0 * r1 * r3)) ^ 2 := by
              field_simp [hr0nz, hr1nz, hr3nz]
              ring
```

Likely tactic repairs if `field_simp` is too aggressive:

```lean
have hrprod : r0 * r1 * r3 ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero hr0nz hr1nz) hr3nz
field_simp [hrprod]
ring_nf
```

### 3.2 Common denominator for three rationals

Avoid abstract `Exists` denominator APIs if they are awkward. Use `Rat.num` and `Rat.den` directly.

Recommended definitions inside the proof:

```lean
let T0 : ℤ := (r0.den : ℤ) * (r1.den : ℤ) * (r3.den : ℤ)
let A0 : ℤ := r0.num * (r1.den : ℤ) * (r3.den : ℤ)
let B0 : ℤ := r1.num * (r0.den : ℤ) * (r3.den : ℤ)
let C0 : ℤ := r3.num * (r0.den : ℤ) * (r1.den : ℤ)
```

Then prove

```lean
r0 = (A0 : ℚ) / (T0 : ℚ)
r1 = (B0 : ℚ) / (T0 : ℚ)
r3 = (C0 : ℚ) / (T0 : ℚ)
```

using the local Rat API. The names to check in the pinned Mathlib are usually:

```lean
#check Rat.num
#check Rat.den
#check Rat.den_nz
#check Rat.num_div_den
#check Rat.num_ne_zero
```

Skeleton:

```lean
private theorem rat_common_den3
    {r0 r1 r3 : ℚ}
    (hr0nz : r0 ≠ 0) (hr1nz : r1 ≠ 0) (hr3nz : r3 ≠ 0) :
    ∃ A0 B0 C0 T0 : ℤ,
      T0 ≠ 0 ∧ A0 ≠ 0 ∧ B0 ≠ 0 ∧ C0 ≠ 0 ∧
      r0 = (A0 : ℚ) / (T0 : ℚ) ∧
      r1 = (B0 : ℚ) / (T0 : ℚ) ∧
      r3 = (C0 : ℚ) / (T0 : ℚ) := by
  let T0 : ℤ := (r0.den : ℤ) * (r1.den : ℤ) * (r3.den : ℤ)
  let A0 : ℤ := r0.num * (r1.den : ℤ) * (r3.den : ℤ)
  let B0 : ℤ := r1.num * (r0.den : ℤ) * (r3.den : ℤ)
  let C0 : ℤ := r3.num * (r0.den : ℤ) * (r1.den : ℤ)
  refine ⟨A0, B0, C0, T0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [T0]
    positivity
  · dsimp [A0]
    exact mul_ne_zero (mul_ne_zero (by exact Rat.num_ne_zero.mpr hr0nz) (by positivity)) (by positivity)
  · dsimp [B0]
    exact mul_ne_zero (mul_ne_zero (by exact Rat.num_ne_zero.mpr hr1nz) (by positivity)) (by positivity)
  · dsimp [C0]
    exact mul_ne_zero (mul_ne_zero (by exact Rat.num_ne_zero.mpr hr3nz) (by positivity)) (by positivity)
  · dsimp [A0, T0]
    rw [Rat.num_div_den r0]
    field_simp [Rat.den_nz]
    ring
  · dsimp [B0, T0]
    rw [Rat.num_div_den r1]
    field_simp [Rat.den_nz]
    ring
  · dsimp [C0, T0]
    rw [Rat.num_div_den r3]
    field_simp [Rat.den_nz]
    ring
```

If `Rat.num_ne_zero.mpr` has a different orientation, replace with:

```lean
have : r0.num ≠ 0 := by
  intro hnum
  apply hr0nz
  rw [Rat.ext_iff]
  simp [hnum]
```

or search:

```lean
#check Rat.num_eq_zero
#check Rat.num_ne_zero
```

### 3.3 Raw cover from common denominator equations

This proof is robust: subtract squareclass equations and clear `T0^2`.

```lean
private theorem rawCoverInt_of_common_den_squareclasses
    {X : ℚ} {d0 d1 d3 A0 B0 C0 T0 : ℤ}
    (hT0 : T0 ≠ 0)
    (hr0 : X = (d0 : ℚ) * (((A0 : ℚ) / (T0 : ℚ)) ^ 2))
    (hr1 : X - 1 = (d1 : ℚ) * (((B0 : ℚ) / (T0 : ℚ)) ^ 2))
    (hr3 : X + 3 = (d3 : ℚ) * (((C0 : ℚ) / (T0 : ℚ)) ^ 2)) :
    CoverInt d0 d1 d3 A0 B0 C0 T0 := by
  constructor
  · norm_num [CoverInt]
    -- Prove equality in ℚ after casting, then exact_mod_cast if needed.
    have hq : ((d0 * A0 ^ 2 - d1 * B0 ^ 2 : ℤ) : ℚ) = (T0 ^ 2 : ℤ) := by
      have hdiff :
          (1 : ℚ) =
            (d0 : ℚ) * (((A0 : ℚ) / (T0 : ℚ)) ^ 2) -
            (d1 : ℚ) * (((B0 : ℚ) / (T0 : ℚ)) ^ 2) := by
        linarith
      have hT0q : (T0 : ℚ) ≠ 0 := by exact_mod_cast hT0
      field_simp [hT0q] at hdiff ⊢
      ring_nf at hdiff ⊢
      exact hdiff.symm
    exact_mod_cast hq
  · have hq : ((d3 * C0 ^ 2 - d0 * A0 ^ 2 : ℤ) : ℚ) = ((3 * T0 ^ 2 : ℤ) : ℚ) := by
      have hdiff :
          (3 : ℚ) =
            (d3 : ℚ) * (((C0 : ℚ) / (T0 : ℚ)) ^ 2) -
            (d0 : ℚ) * (((A0 : ℚ) / (T0 : ℚ)) ^ 2) := by
        linarith
      have hT0q : (T0 : ℚ) ≠ 0 := by exact_mod_cast hT0
      field_simp [hT0q] at hdiff ⊢
      ring_nf at hdiff ⊢
      exact hdiff.symm
    exact_mod_cast hq
```

If `exact_mod_cast` struggles with powers, state the integer goal and use `norm_num`/`ring_nf` after converting the rational equality. A reliable fallback is:

```lean
norm_num at hq
exact hq
```

because `Int.cast_inj` into `ℚ` is available.

### 3.4 Four-variable gcd normalization

Use a small local gcd utility. Do not try to use `Int.gcd` directly if its `Nat` return type causes sign clutter; `natAbs` makes positivity and divisibility cleaner.

```lean
private def gcd4 (A B C T : ℤ) : ℕ :=
  Nat.gcd (Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs) T.natAbs
```

API targets:

```lean
#check Int.natAbs
#check Int.natAbs_dvd_natAbs
#check Int.dvd_natAbs
#check Nat.gcd_dvd_left
#check Nat.gcd_dvd_right
#check Nat.dvd_gcd
#check Int.ediv_mul_cancel
#check Int.mul_ediv_cancel'
```

Recommended proof shape for divisibility projections:

```lean
private theorem gcd4_dvd_A {A B C T : ℤ} :
    ((gcd4 A B C T : ℕ) : ℤ) ∣ A := by
  -- prove `(gcd4 A B C T) ∣ A.natAbs` by Nat gcd projections;
  -- then convert to integer divisibility of `A` using natAbs API.
  -- Skeleton:
  -- have hnat : gcd4 A B C T ∣ A.natAbs := ...
  -- exact Int.ofNat_dvd.mp hnat  -- if available
  -- or use `Int.dvd_natAbs` / `Int.natAbs_dvd_natAbs` bridge.
  ...
```

Because API names vary across pinned Mathlib versions, an often easier route is to define a predicate-level gcd package and prove it by Nat gcd once:

```lean
private def IsGCD4 (g A B C T : ℤ) : Prop :=
  0 < g ∧ g ∣ A ∧ g ∣ B ∧ g ∣ C ∧ g ∣ T ∧
    ∀ d : ℤ, d ∣ A → d ∣ B → d ∣ C → d ∣ T → d ∣ g
```

Then prove one theorem:

```lean
private theorem exists_isGCD4 {A B C T : ℤ} (hT : T ≠ 0) :
    ∃ g : ℤ, IsGCD4 g A B C T
```

This can still use `g = gcd4 A B C T`, but downstream normalization only consumes the `IsGCD4` package and becomes much cleaner.

### 3.5 Primitive normalization by gcd

This is the key primitive step. I recommend proving it from the abstract `IsGCD4` package, then using the concrete gcd theorem only once.

```lean
private theorem primitive_div_isGCD4
    {A0 B0 C0 T0 g : ℤ}
    (hg : IsGCD4 g A0 B0 C0 T0) :
    ∃ A B C T : ℤ,
      A0 = g * A ∧ B0 = g * B ∧ C0 = g * C ∧ T0 = g * T ∧
      PrimitiveInt4 A B C T := by
  rcases hg with ⟨hgpos, hgA, hgB, hgC, hgT, hgreat⟩
  rcases hgA with ⟨A, hA⟩
  rcases hgB with ⟨B, hB⟩
  rcases hgC with ⟨C, hC⟩
  rcases hgT with ⟨T, hT⟩
  refine ⟨A, B, C, T, hA.symm, hB.symm, hC.symm, hT.symm, ?_⟩
  intro p hp hall
  rcases hall with ⟨hpA, hpB, hpC, hpT⟩

  -- `p*g` divides each original coordinate.
  have hpgA : ((p : ℤ) * g) ∣ A0 := by
    rcases hpA with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [hA, ha]
    ring
  have hpgB : ((p : ℤ) * g) ∣ B0 := by
    rcases hpB with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rw [hB, hb]
    ring
  have hpgC : ((p : ℤ) * g) ∣ C0 := by
    rcases hpC with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [hC, hc]
    ring
  have hpgT : ((p : ℤ) * g) ∣ T0 := by
    rcases hpT with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [hT, ht]
    ring

  have hpg_dvd_g : ((p : ℤ) * g) ∣ g := hgreat ((p : ℤ) * g) hpgA hpgB hpgC hpgT
  rcases hpg_dvd_g with ⟨k, hk⟩
  have hg_ne : g ≠ 0 := ne_of_gt hgpos
  have hpunit : IsUnit (p : ℤ) := by
    -- hk : g = (p*g)*k.  Cancel nonzero g to get `1 = p*k`.
    have hcancel : (1 : ℤ) = (p : ℤ) * k := by
      apply mul_left_cancel₀ hg_ne
      calc
        g * 1 = g := by ring
        _ = (p : ℤ) * g * k := hk
        _ = g * ((p : ℤ) * k) := by ring
    exact ⟨k, hcancel.symm⟩

  -- Contradict primality of `p`: a prime natural is not a unit as an integer.
  have hpgt1 : 1 < p := hp.one_lt
  rcases Int.isUnit_iff.mp hpunit with hp_one | hp_neg_one
  · have : (p : ℤ) ≠ 1 := by exact_mod_cast (ne_of_gt hpgt1)
    exact this hp_one
  · have : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
    linarith
```

This proof avoids needing to reason about `A0 / g` directly. It extracts quotient witnesses from divisibility and proves they are primitive.

Nonzero after normalization:

```lean
private theorem nonzero_of_eq_g_mul
    {x g y : ℤ} (hx : x ≠ 0) (hg : g ≠ 0) (hxy : x = g * y) : y ≠ 0 := by
  intro hy
  apply hx
  rw [hxy, hy]
  ring
```

Rational ratio preservation after normalization:

```lean
private theorem rat_div_eq_of_common_factor
    {x t g y u : ℤ}
    (hg : g ≠ 0) (hu : u ≠ 0)
    (hx : x = g * y) (ht : t = g * u) :
    (x : ℚ) / (t : ℚ) = (y : ℚ) / (u : ℚ) := by
  have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hg
  have huq : (u : ℚ) ≠ 0 := by exact_mod_cast hu
  rw [hx, ht]
  field_simp [hgq, huq]
  ring
```

### 3.6 Homogeneous cover equation descends

```lean
private theorem coverInt_div_common_factor
    {d0 d1 d3 A0 B0 C0 T0 A B C T g : ℤ}
    (hg : g ≠ 0)
    (hA : A0 = g * A) (hB : B0 = g * B)
    (hC : C0 = g * C) (hT : T0 = g * T)
    (hcover : CoverInt d0 d1 d3 A0 B0 C0 T0) :
    CoverInt d0 d1 d3 A B C T := by
  rcases hcover with ⟨h1, h2⟩
  constructor
  · have hmul : g ^ 2 * (d0 * A ^ 2 - d1 * B ^ 2 - T ^ 2) = 0 := by
      rw [hA, hB, hT] at h1
      nlinarith [h1]
    have hg2 : g ^ 2 ≠ 0 := pow_ne_zero 2 hg
    have hzero : d0 * A ^ 2 - d1 * B ^ 2 - T ^ 2 = 0 :=
      (mul_eq_zero.mp hmul).resolve_left hg2
    linarith
  · have hmul : g ^ 2 * (d3 * C ^ 2 - d0 * A ^ 2 - 3 * T ^ 2) = 0 := by
      rw [hA, hC, hT] at h2
      nlinarith [h2]
    have hg2 : g ^ 2 ≠ 0 := pow_ne_zero 2 hg
    have hzero : d3 * C ^ 2 - d0 * A ^ 2 - 3 * T ^ 2 = 0 :=
      (mul_eq_zero.mp hmul).resolve_left hg2
    linarith
```

If `nlinarith` is slow, replace the two `hmul` blocks by `ring_nf at h1 ⊢` and exact the normalized expression.

## 4. Final residual theorem skeleton

```lean
namespace MazurProof.RationalPointsN12

theorem commonDenomSquareclassRepsToPrimitiveCoverInt :
    CommonDenomSquareclassRepsToPrimitiveCoverIntStatement := by
  intro X Y d0 d1 d3 r0 r1 r3 hE hY hd0 hd1 hd3 hr0nz hr1nz hr3nz h0 h1 h3

  have hprod : ProductSquareclassCondition d0 d1 d3 :=
    productSquareclassCondition_of_curve_squareclasses
      (X:=X) (Y:=Y) (d0:=d0) (d1:=d1) (d3:=d3)
      (r0:=r0) (r1:=r1) (r3:=r3)
      hE hY hr0nz hr1nz hr3nz h0 h1 h3

  obtain ⟨A0, B0, C0, T0, hT0, hA0, hB0, hC0, hr0, hr1, hr3⟩ :=
    rat_common_den3 (r0:=r0) (r1:=r1) (r3:=r3) hr0nz hr1nz hr3nz

  have h0' : X = (d0 : ℚ) * (((A0 : ℚ) / (T0 : ℚ)) ^ 2) := by
    rw [h0, hr0]
  have h1' : X - 1 = (d1 : ℚ) * (((B0 : ℚ) / (T0 : ℚ)) ^ 2) := by
    rw [h1, hr1]
  have h3' : X + 3 = (d3 : ℚ) * (((C0 : ℚ) / (T0 : ℚ)) ^ 2) := by
    rw [h3, hr3]

  have hcover0 : CoverInt d0 d1 d3 A0 B0 C0 T0 :=
    rawCoverInt_of_common_den_squareclasses
      (X:=X) (d0:=d0) (d1:=d1) (d3:=d3)
      (A0:=A0) (B0:=B0) (C0:=C0) (T0:=T0)
      hT0 h0' h1' h3'

  obtain ⟨A, B, C, T, hT, hA, hB, hC, hprim, hrat0, hrat1, hrat3, hcover⟩ :=
    primitiveCoverInt_of_rawCoverInt
      (d0:=d0) (d1:=d1) (d3:=d3)
      (A0:=A0) (B0:=B0) (C0:=C0) (T0:=T0)
      hT0 hA0 hB0 hC0 hcover0

  refine ⟨d0, d1, d3, hd0, hd1, hd3, hprod, A, B, C, T,
    hT, hA, hB, hC, hprim, ?_, ?_, ?_, hcover⟩
  · rw [h0, hr0, hrat0]
  · rw [h1, hr1, hrat1]
  · rw [h3, hr3, hrat3]

end MazurProof.RationalPointsN12
```

If the local theorem must have exactly the proposition name, use whichever naming style the file uses. Avoid naming the theorem exactly the same as the `def` if Lean complains about name shadowing; a good theorem name is:

```lean
theorem commonDenomSquareclassRepsToPrimitiveCoverIntStatement_proof :
    CommonDenomSquareclassRepsToPrimitiveCoverIntStatement := by
  ...
```

## 5. Import/cycle guidance

Do not import `N12FourSquaresAP` into `N12E1FullCoverExtraction.lean`. This proof only needs:

```lean
import Mathlib.Tactic
```

plus whatever local file currently defines the displayed E1 full-cover definitions. If gcd helpers are reused elsewhere, move only generic lemmas to a low-level file such as:

```text
FLT/Assumptions/MazurProof/IntGcd4RatClearDenoms.lean
```

That utility should import only `Mathlib.Tactic`, not downstream N=12 obstruction or AP files. Suggested contents:

```lean
namespace MazurProof.RationalPointsN12

private def gcd4 ...
private def IsGCD4 ...
private theorem exists_isGCD4 ...
private theorem primitive_div_isGCD4 ...
private theorem rat_div_eq_of_common_factor ...
private theorem rat_common_den3 ...

end MazurProof.RationalPointsN12
```

Keep `CoverInt`, `PrimitiveInt4`, `E1FullCoverCurve`, and `E1FullCoverIntData` in the extraction/full-cover files, not in the generic utility, to avoid dependency cycles.

## 6. Main API pitfalls

* `Rat.den` is a `Nat`; cast it through `ℤ` for integer numerator construction and through `ℚ` for `field_simp`.
* `Rat.num` may be zero iff the rational is zero. Use `Rat.num_ne_zero` / `Rat.num_eq_zero`, or prove the local fact by `Rat.ext` if names differ.
* Avoid integer `/` for primitive normalization unless you have divisibility packaged. Extract quotient witnesses from `g ∣ A0`, etc.; this avoids fragile `ediv` simplification.
* For proving primitive after gcd division, use the maximality clause `∀ d, d∣A0→d∣B0→d∣C0→d∣T0→d∣g`. Then a prime dividing all quotients gives `(p:ℤ)*g ∣ g`, contradicting `p.Prime`.
* For nonzero normalized coordinates, use `x = g*y`, `x ≠ 0`, `g ≠ 0`; do not reason through `/`.
* For cover descent, exploit homogeneity of degree two; substitute `A0=g*A`, etc., get `g^2 * residual = 0`, and cancel `g^2`.
* `ProductSquareclassCondition` should be proved before denominator clearing; it is cleaner in `ℚ` and uses `Y ≠ 0` plus `r0*r1*r3 ≠ 0`.
