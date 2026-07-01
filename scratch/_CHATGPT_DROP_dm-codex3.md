# Q2769: certificate table for the full 2-cover squareclass triples

Target residual: `E1CoverIntSurvivingTriplesStatement`.

Equations:

```text
d0*A^2 - d1*B^2 = T^2
d3*C^2 - d0*A^2 = 3*T^2
```

with primitive integer projective tuple `(A,B,C,T)`, all nonzero. For local obstruction certificates below, nonzero is not needed; primitivity is reduced to: **not all of `A,B,C,T` are even**.

Squareclass set:

```lean
def S23 : List Int := [1, -1, 2, -2, 3, -3, 6, -6]
```

Expected final surviving triples, confirmed by this certificate plan:

```lean
[(3,2,6), (-1,-2,2), (1,1,1), (-3,-1,3)]
```

## 1. Admissible squareclass triples before local obstruction

The product squareclass condition is exactly that `d0*d1*d3` is trivial in
`ℚˣ/(ℚˣ)^2`, i.e. positive with even 2-adic and 3-adic exponents.
Equivalently, for each row `d0` and column `d1`, `d3` is the following entry.
Every table entry denotes the admissible ordered triple `(d0,d1,d3)`.

Columns are `d1 = 1, -1, 2, -2, 3, -3, 6, -6`.

| d0 \ d1 | 1 | -1 | 2 | -2 | 3 | -3 | 6 | -6 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1  | 1 | -1 | 2 | -2 | 3 | -3 | 6 | -6 |
| -1 | -1 | 1 | -2 | 2 | -3 | 3 | -6 | 6 |
| 2  | 2 | -2 | 1 | -1 | 6 | -6 | 3 | -3 |
| -2 | -2 | 2 | -1 | 1 | -6 | 6 | -3 | 3 |
| 3  | 3 | -3 | 6 | -6 | 1 | -1 | 2 | -2 |
| -3 | -3 | 3 | -6 | 6 | -1 | 1 | -2 | 2 |
| 6  | 6 | -6 | 3 | -3 | 2 | -2 | 1 | -1 |
| -6 | -6 | 6 | -3 | 3 | -2 | 2 | -1 | 1 |

There are `64` admissible triples.

Lean-friendly squareclass product predicate:

```lean
def sqClassBit (d : Int) : Bool × Bool × Bool :=
  (d < 0, (2 : Int) ∣ d, (3 : Int) ∣ d)

-- For `S23`, the bit triple `(sign, two, three)` is enough.
def sqClassProductTrivial (d0 d1 d3 : Int) : Bool :=
  let s0 := sqClassBit d0
  let s1 := sqClassBit d1
  let s3 := sqClassBit d3
  decide (s0.1 != s1.1 != s3.1 = false) -- better implemented by explicit xor bits
```

For implementation, I recommend not proving this predicate abstractly. Hard-code the 64-table above as data and use `native_decide` for membership.

## 2. Real sign obstruction

Real obstruction is simple and complete at infinity:

```text
A^2,B^2,C^2,T^2 > 0.
If d3 < 0, no real solution.
If d3 > 0, real signs alone do not obstruct.
```

Reason:

* If `d3 < 0`, then by the product squareclass condition `d0` and `d1` have opposite signs.
* If `d0 > 0, d1 < 0`, then the second equation has `d3*C^2 - d0*A^2 < 0`, contradiction.
* If `d0 < 0, d1 > 0`, then the first equation has `d0*A^2 - d1*B^2 < 0`, contradiction.

So the real survivors are exactly the admissible triples with `d3 > 0`:

```lean
def realSurvivors : List (Int × Int × Int) :=
  [ (1,1,1), (1,2,2), (1,3,3), (1,6,6),
    (-1,-1,1), (-1,-2,2), (-1,-3,3), (-1,-6,6),
    (2,1,2), (2,2,1), (2,3,6), (2,6,3),
    (-2,-1,2), (-2,-2,1), (-2,-3,6), (-2,-6,3),
    (3,1,3), (3,2,6), (3,3,1), (3,6,2),
    (-3,-1,3), (-3,-2,6), (-3,-3,1), (-3,-6,2),
    (6,1,6), (6,2,3), (6,3,2), (6,6,1),
    (-6,-1,6), (-6,-2,3), (-6,-3,2), (-6,-6,1) ]
```

The real-obstructed triples are exactly the admissible triples with `d3 < 0`:

```lean
def realObstructed : List (Int × Int × Int) :=
  [ (1,-1,-1), (1,-2,-2), (1,-3,-3), (1,-6,-6),
    (-1,1,-1), (-1,2,-2), (-1,3,-3), (-1,6,-6),
    (2,-1,-2), (2,-2,-1), (2,-3,-6), (2,-6,-3),
    (-2,1,-2), (-2,2,-1), (-2,3,-6), (-2,6,-3),
    (3,-1,-3), (3,-2,-6), (3,-3,-1), (3,-6,-2),
    (-3,1,-3), (-3,2,-6), (-3,3,-1), (-3,6,-2),
    (6,-1,-6), (6,-2,-3), (6,-3,-2), (6,-6,-1),
    (-6,1,-6), (-6,2,-3), (-6,3,-2), (-6,6,-1) ]
```

Lean real-sign lemma shape:

```lean
theorem cover_real_obstruction_of_d3_neg
    {d0 d1 d3 A B C T : Int}
    (hprod : d0 * d1 * d3 > 0) -- or the squareclass-table fact giving opposite signs
    (hd3 : d3 < 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hT : T ≠ 0)
    (h1 : d0 * A^2 - d1 * B^2 = T^2)
    (h2 : d3 * C^2 - d0 * A^2 = 3 * T^2) :
    False := by
  -- In table implementation, split on `d0,d1,d3`; each case is `nlinarith`
  -- using `sq_pos_of_ne_zero` for A,B,C,T.
  native_decide
```

In practice, avoid a general sign proof: use the `realObstructed` table and prove each row by `norm_num`/`nlinarith` after case-splitting.

## 3. Finite local obstruction predicate

Use this finite predicate for a modulus `M = 4, 8, 16`.

```lean
def evenFin {M : Nat} (x : Fin M) : Prop :=
  x.val % 2 = 0

def coverResidueSol (M : Nat) (d0 d1 d3 : Int) : Prop :=
  ∃ A B C T : Fin M,
    ¬ (evenFin A ∧ evenFin B ∧ evenFin C ∧ evenFin T) ∧
    (d0 * (A.val : Int)^2 - d1 * (B.val : Int)^2 - (T.val : Int)^2) % (M : Int) = 0 ∧
    (d3 * (C.val : Int)^2 - d0 * (A.val : Int)^2 - 3 * (T.val : Int)^2) % (M : Int) = 0
```

Then each finite obstruction certificate is simply:

```lean
example : ¬ coverResidueSol 8 1 2 2 := by native_decide
example : ¬ coverResidueSol 16 1 3 3 := by native_decide
```

The primitive condition is exactly the parity clause: if an integer tuple is primitive, not all entries are even, hence its residue tuple satisfies the same clause for every even modulus.

## 4. Finite obstruction table for all non-surviving real triples

The following `28` real-surviving triples are **not** final survivors and are killed by the indicated modulus. These are minimal among `{4,8,16}` for this predicate, but using uniform modulus `16` for all rows also works.

### Mod 4 kills 20 triples

```lean
def mod4Killed : List (Int × Int × Int) :=
  [ (-1,-1,1), (-1,-3,3),
    (2,1,2), (2,2,1), (2,3,6), (2,6,3),
    (-2,-1,2), (-2,-2,1), (-2,-3,6), (-2,-6,3),
    (3,1,3), (3,3,1),
    (6,1,6), (6,2,3), (6,3,2), (6,6,1),
    (-6,-1,6), (-6,-2,3), (-6,-3,2), (-6,-6,1) ]
```

Certificate examples:

```lean
example : ¬ coverResidueSol 4 (-1) (-1) 1 := by native_decide
example : ¬ coverResidueSol 4 2 1 2 := by native_decide
example : ¬ coverResidueSol 4 6 3 2 := by native_decide
```

### Mod 8 kills 6 further triples

```lean
def mod8Killed : List (Int × Int × Int) :=
  [ (1,2,2), (1,6,6), (-1,-6,6),
    (3,6,2), (-3,-2,6), (-3,-6,2) ]
```

Certificate examples:

```lean
example : ¬ coverResidueSol 8 1 2 2 := by native_decide
example : ¬ coverResidueSol 8 (-3) (-2) 6 := by native_decide
```

### Mod 16 kills the last 2 triples

```lean
def mod16Killed : List (Int × Int × Int) :=
  [ (1,3,3), (-3,-3,1) ]
```

Certificate examples:

```lean
example : ¬ coverResidueSol 16 1 3 3 := by native_decide
example : ¬ coverResidueSol 16 (-3) (-3) 1 := by native_decide
```

### Uniform certificate alternative

For simplest Lean, skip the minimal-modulus table and use one uniform finite table:

```lean
def finiteKilledBy16 : List (Int × Int × Int) :=
  mod4Killed ++ mod8Killed ++ mod16Killed
```

Then prove each row by:

```lean
example : ¬ coverResidueSol 16 2 1 2 := by native_decide
example : ¬ coverResidueSol 16 1 2 2 := by native_decide
example : ¬ coverResidueSol 16 1 3 3 := by native_decide
```

This is less elegant but least risky.

## 5. Final survivors

After real obstruction and finite obstruction, the remaining real-surviving triples are exactly:

```lean
def coverSurvivors : List (Int × Int × Int) :=
  [ (3,2,6), (-1,-2,2), (1,1,1), (-3,-1,3) ]
```

They are not killed by the parity-mod predicates. For instance, these residue witnesses exist mod 16:

```text
(3,2,6):     A=B=C=T=1
(-1,-2,2):   A=B=C=T=1
(1,1,1):     A=1, B=0, C=2, T=1
(-3,-1,3):   A=0, B=1, C=1, T=1
```

These witnesses are only local sanity checks; they are not needed for the exclusion proof.

## 6. Lean statement plan for `E1CoverIntSurvivingTriplesStatement`

Suggested implementation shape:

```lean
def IsS23 (d : Int) : Prop := d ∈ S23

def ProductSquareclassOK (d0 d1 d3 : Int) : Prop :=
  (d0, d1, d3) ∈ admissibleTriplesTable

def CoverSurvives (d0 d1 d3 : Int) : Prop :=
  (d0, d1, d3) ∈ coverSurvivors

def FullCoverEq (d0 d1 d3 A B C T : Int) : Prop :=
  d0*A^2 - d1*B^2 = T^2 ∧
  d3*C^2 - d0*A^2 = 3*T^2

def PrimitiveParity (A B C T : Int) : Prop :=
  ¬ (Even A ∧ Even B ∧ Even C ∧ Even T)

theorem finite_obstruction_of_coverResidueSol_false
    {M : Nat} {d0 d1 d3 A B C T : Int}
    (hM : M = 4 ∨ M = 8 ∨ M = 16)
    (hno : ¬ coverResidueSol M d0 d1 d3)
    (hprim : PrimitiveParity A B C T)
    (h1 : d0*A^2 - d1*B^2 = T^2)
    (h2 : d3*C^2 - d0*A^2 = 3*T^2) :
    False := by
  -- Reduce A,B,C,T to Fin M by `% M`; equations descend modulo M.
  -- The primitive parity gives the `not all even` clause.
  sorry

theorem E1CoverIntSurvivingTriplesStatement_proof :
    E1CoverIntSurvivingTriplesStatement := by
  intro d0 d1 d3 hS0 hS1 hS3 hprod A B C T hprim hnonzero h1 h2
  -- Case split by `admissibleTriplesTable`.
  -- 1. If d3 < 0: real sign obstruction.
  -- 2. If row is in finiteKilled table: use corresponding `native_decide` no-residue lemma.
  -- 3. Remaining rows are the four survivors.
  native_decide
```

For the finite step, if you want to avoid a general modulo-lifting lemma, prove a theorem per killed triple directly by reducing integer squares modulo `M` using `omega`/`norm_num` and parity cases. But the `coverResidueSol` route is much cleaner.

## 7. Symmetry reductions

Recommended: **do not use symmetry reductions** beyond the product-squareclass table and the real sign criterion. The two equations are asymmetric in `(d0,d1,d3)` because `d0*A^2` appears in both equations and the second equation has the coefficient `3*T^2`. Any symmetry would need proof and will likely cost more Lean effort than the 28 `native_decide` finite rows.

Safe reductions:

1. Product squareclass table reduces `8^3 = 512` to `64` triples.
2. Real sign `d3 < 0` kills `32` triples.
3. Uniform `mod 16` predicate kills the `28` non-surviving real triples.
4. The remaining `4` are exactly `coverSurvivors`.

This is the lowest-risk Lean implementation path.
