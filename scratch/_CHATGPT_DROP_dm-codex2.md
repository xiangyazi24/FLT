# Q2724 dm-codex2: N12FourSquaresAP route for the divided branch

## Connector audit status

I could not confirm the requested existing Lean file from the connected repository. Through the GitHub connector:

- `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean` returned `404` on `scratch`.
- The same path had previously returned `404` on the default branch.
- Code search in `xiangyazi24/FLT` for `N12FourSquaresAP`, `FourSquaresAP`, and `pythagoreanQuarticRhs` returned no hits.

So I cannot honestly name an already-existing theorem from `N12FourSquaresAP.lean`. The answer below therefore gives the exact wrapper/interface I would add and the concrete proof route. Where a theorem is described as “use this”, it means “make this the local API boundary and prove it from the actual AP theorem once the WIP file is visible”; I am not claiming repo-confirmed `#check` output for that theorem name.

## 1. Four-squares AP theorem/interface to use

For the divided `m` even branch, the downstream code should not depend on the internal shape of the four-squares AP proof. The minimal API should be this wrapper:

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- No nonconstant four integer squares in arithmetic progression, in the exact
midpoint form needed by the divided `m` even branch.

The two hypotheses say that `c^2, b^2, d^2, a^2` are in arithmetic progression.
The conclusion is deliberately only equality of squares; signs are handled later
from the positive factor package. -/
def FourSquaresAPCollapseStatement : Prop :=
  ∀ {a b c d : ℤ},
    c ^ 2 + d ^ 2 = 2 * b ^ 2 →
    b ^ 2 + a ^ 2 = 2 * d ^ 2 →
    a ^ 2 = d ^ 2 ∧ d ^ 2 = b ^ 2 ∧ b ^ 2 = c ^ 2

end MazurProof.RationalPointsN12
```

If the existing file has a theorem for a centered primitive AP, prove this wrapper from it once, then make all divided-branch code depend only on `FourSquaresAPCollapseStatement` or on the theorem implementation of that statement, e.g.

```lean
theorem four_squares_ap_collapse_of_midpoint :
    FourSquaresAPCollapseStatement := by
  -- prove from the existing centered/primitive AP theorem
```

I would **not** thread a primitive/centered AP theorem directly into the divided branch. The divided branch naturally produces the two midpoint identities above; any primitive normalization is an implementation detail of the AP file.

## 2. Lean-friendly skeleton for `DividedMEvenFactorsUnitStatement`

The target statement from your WIP is:

```lean
def DividedMEvenFactorsUnitStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    DividedSquareBranch A N S m n →
    Even m →
    DividedSqBranchMEvenFactors m n →
    A = 1 ∧ N = 1 ∧ S = 1
```

The proof should split into three small bridges.

### Bridge A: `MEvenFactors` gives the two AP midpoint identities

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- Exact AP identities extracted from the `m` even divided factor package. -/
def DividedMEvenFactorsAPIdentitiesStatement : Prop :=
  ∀ {m n a b c d : ℤ},
    m - n = a ^ 2 →
    m + n = 3 * b ^ 2 →
    n = c ^ 2 →
    2 * m - n = 3 * d ^ 2 →
    c ^ 2 + d ^ 2 = 2 * b ^ 2 ∧
      b ^ 2 + a ^ 2 = 2 * d ^ 2

end MazurProof.RationalPointsN12
```

The proof body is just `nlinarith` after destructing the factor package:

```lean
rcases hf with ⟨a, b, c, d, ha, hb, hc, hd, hmn, hmpn, hn, h2mn⟩

have hap1 : c ^ 2 + d ^ 2 = 2 * b ^ 2 := by
  nlinarith [hmpn, hn, h2mn]

have hap2 : b ^ 2 + a ^ 2 = 2 * d ^ 2 := by
  nlinarith [hmn, hmpn, h2mn]
```

Algebra check:

- From `m+n = 3*b^2`, `n = c^2`, and `2*m-n = 3*d^2`, subtracting the last equation from twice the first gives `3*c^2 + 3*d^2 = 6*b^2`, hence `c^2+d^2=2*b^2`.
- From `m-n = a^2`, `m+n = 3*b^2`, and `2*m-n = 3*d^2`, the identity `2*(2*m-n) = (m+n) + 3*(m-n)` gives `2*d^2 = b^2+a^2`.

### Bridge B: AP collapse plus coprimality gives `m = 2`, `n = 1`

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- The `m` even divided factor package collapses to the unique coprime solution
`m = 2`, `n = 1`, assuming the four-squares AP collapse wrapper. -/
def DividedMEvenFactorsMNUnitStatement : Prop :=
  ∀ {m n : ℤ},
    IsCoprime m n →
    DividedSqBranchMEvenFactors m n →
    m = 2 ∧ n = 1

end MazurProof.RationalPointsN12
```

Core proof skeleton:

```lean
rcases hf with ⟨a, b, c, d, ha, hb, hc, hd, hmn, hmpn, hn, h2mn⟩

have hap1 : c ^ 2 + d ^ 2 = 2 * b ^ 2 := by
  nlinarith [hmpn, hn, h2mn]
have hap2 : b ^ 2 + a ^ 2 = 2 * d ^ 2 := by
  nlinarith [hmn, hmpn, h2mn]

-- Use the wrapper from the AP file.
have hsq : a ^ 2 = d ^ 2 ∧ d ^ 2 = b ^ 2 ∧ b ^ 2 = c ^ 2 :=
  four_squares_ap_collapse_of_midpoint hap1 hap2

have ha2c2 : a ^ 2 = c ^ 2 := by
  calc
    a ^ 2 = d ^ 2 := hsq.1
    _ = b ^ 2 := hsq.2.1
    _ = c ^ 2 := hsq.2.2

have hn_a : n = a ^ 2 := by
  calc
    n = c ^ 2 := hn
    _ = a ^ 2 := ha2c2.symm

have hm_a : m = 2 * a ^ 2 := by
  nlinarith [hmn, hn_a]

have ha2_dvd_m : a ^ 2 ∣ m := by
  refine ⟨2, ?_⟩
  rw [hm_a]
  ring

have ha2_dvd_n : a ^ 2 ∣ n := by
  refine ⟨1, ?_⟩
  rw [hn_a]
  ring

-- Mathlib API expected here:
have ha2_unit : IsUnit (a ^ 2) :=
  hcop.isUnit_of_dvd ha2_dvd_m ha2_dvd_n

have ha2_pos : 0 < a ^ 2 := by
  positivity

have ha2_one : a ^ 2 = 1 := by
  rw [Int.isUnit_iff] at ha2_unit
  rcases ha2_unit with ha2_one | ha2_neg_one
  · exact ha2_one
  · have : (0 : ℤ) < -1 := by
      simpa [ha2_neg_one] using ha2_pos
    omega

have hn1 : n = 1 := by
  rw [hn_a, ha2_one]

have hm2 : m = 2 := by
  rw [hm_a, ha2_one]
  norm_num
```

Notes:

- `Even m` is not used once `DividedSqBranchMEvenFactors m n` has been produced. It is still harmless in `DividedMEvenFactorsUnitStatement`, because it documents which split branch produced the factor package.
- If `hcop.isUnit_of_dvd` is not found under method notation, use the namespace form for the same Mathlib theorem, usually `IsCoprime.isUnit_of_dvd hcop ha2_dvd_m ha2_dvd_n`.
- The only nontrivial Mathlib dependency in this bridge is the `IsCoprime` common-divisor-to-unit API.

### Bridge C: `m = 2`, `n = 1` and divided branch equations give `A=N=S=1`

This bridge should not know anything about APs or factor packages.

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- Positivity projection needed from `PositivePrimitiveEisensteinBadUnordered`.
If the local definition is a conjunction, this should be a one-line `rcases`/`aesop` lemma. -/
def PositivePrimitiveEisensteinBadUnorderedPosStatement : Prop :=
  ∀ {A N S : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    0 < A ∧ 0 < N ∧ 0 < S

/-- Once the divided branch reaches `(m,n)=(2,1)`, the branch equations force
`A=N=S=1`. -/
def DividedSquareBranchUnitOfMNStatement : Prop :=
  ∀ {A N S m n : ℤ},
    0 < A →
    0 < N →
    DividedSquareBranch A N S m n →
    m = 2 →
    n = 1 →
    A = 1 ∧ N = 1 ∧ S = 1

end MazurProof.RationalPointsN12
```

The branch-equation proof body is essentially:

```lean
rcases hbr with ⟨hnpos, hnm, hcop, h3, hAeq, hNeq, hSeq⟩

have hA_sq : A ^ 2 = 1 := by
  rw [hm2, hn1] at hAeq
  norm_num at hAeq
  exact hAeq

have hN_sq : N ^ 2 = 1 := by
  rw [hm2, hn1] at hNeq
  norm_num at hNeq
  exact hNeq

have hA1 : A = 1 := by
  rcases (sq_eq_one_iff.mp hA_sq) with hA1 | hAneg
  · exact hA1
  · omega

have hN1 : N = 1 := by
  rcases (sq_eq_one_iff.mp hN_sq) with hN1 | hNneg
  · exact hN1
  · omega

have hS1 : S = 1 := by
  rw [hm2, hn1] at hSeq
  norm_num at hSeq
  omega

exact ⟨hA1, hN1, hS1⟩
```

Then the final `DividedMEvenFactorsUnitStatement` proof is only orchestration:

```lean
intro A N S m n hprim hbr hmEven hf
obtain ⟨hApos, hNpos, hSpos⟩ := positivePrimitiveEisensteinBadUnordered_pos hprim
rcases hbr with ⟨hnpos, hnm, hcop, h3, hAeq, hNeq, hSeq⟩
have hbr_saved : DividedSquareBranch A N S m n :=
  ⟨hnpos, hnm, hcop, h3, hAeq, hNeq, hSeq⟩
obtain ⟨hm2, hn1⟩ := divided_mEven_factors_mn_unit hcop hf
exact dividedSquareBranch_unit_of_m_eq_two_n_eq_one hApos hNpos hbr_saved hm2 hn1
```

## 3. Lean-friendly proof of the mod-4 lemma

This one is independent of the project definitions and should live near the MOdd contradiction.

```lean
import Mathlib.Tactic

theorem no_oddC_three_square_sum {a b c : ℤ} :
    Odd c → a ^ 2 + c ^ 2 = 3 * b ^ 2 → False := by
  intro hc h
  rcases hc with ⟨k, rfl⟩
  rcases Int.even_or_odd a with ha | ha
  · rcases ha with ⟨r, rfl⟩
    rcases Int.even_or_odd b with hb | hb
    · rcases hb with ⟨s, rfl⟩
      ring_nf at h
      omega
    · rcases hb with ⟨s, rfl⟩
      ring_nf at h
      omega
  · rcases ha with ⟨r, rfl⟩
    rcases Int.even_or_odd b with hb | hb
    · rcases hb with ⟨s, rfl⟩
      ring_nf at h
      omega
    · rcases hb with ⟨s, rfl⟩
      ring_nf at h
      omega
```

If `Int.even_or_odd` is not in the imported namespace in this project, the same proof usually works with the unqualified theorem:

```lean
rcases even_or_odd a with ha | ha
```

The proof is just the mod-4 argument encoded by parity witnesses:

- `c` odd gives `c^2 ≡ 1 mod 4`.
- `a^2` is `0` or `1 mod 4`, so `a^2+c^2` is `1` or `2 mod 4`.
- `3*b^2` is `0` or `3 mod 4`.
- No residue matches.

For the MOdd factor package, the bridge theorem should be:

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- The odd-`m` divided factor package is impossible once the divided branch has
forced `n` odd. -/
def DividedMOddFactorsImpossibleStatement : Prop :=
  ∀ {m n : ℤ},
    Odd n →
    DividedSqBranchMOddFactors m n →
    False

end MazurProof.RationalPointsN12
```

Core proof skeleton:

```lean
rcases hf with ⟨a, b, c, d, ha, hb, hc, hd, hmn, hmpn, hn, h2mn⟩

have hodd_c : Odd c := by
  -- From `Odd n` and `n = c^2`.
  -- A robust route is contraposition: if `Even c`, then `Even (c^2)`, hence `Even n`.
  -- This contradicts `Odd n`.

have hsum : a ^ 2 + c ^ 2 = 3 * b ^ 2 := by
  -- From `m-n = 2*a^2`, `m+n = 6*b^2`, and `n = c^2`.
  nlinarith [hmn, hmpn, hn]

exact no_oddC_three_square_sum hodd_c hsum
```

Algebra check for `hsum`:

`m-n = 2*a^2`, `m+n = 6*b^2`, and `n=c^2` imply
`(m+n) - (m-n) = 2*n`, hence `6*b^2 - 2*a^2 = 2*c^2`, so `a^2+c^2=3*b^2`.

## 4. Shorter existing theorem?

I cannot name a shorter existing theorem from the connected repo, because the requested file and theorem names were not visible to the connector. In the local WIP, search for a theorem whose conclusion is equivalent to one of these shapes:

```lean
∀ {a b c d : ℤ},
  c ^ 2 + d ^ 2 = 2 * b ^ 2 →
  b ^ 2 + a ^ 2 = 2 * d ^ 2 →
  a ^ 2 = d ^ 2 ∧ d ^ 2 = b ^ 2 ∧ b ^ 2 = c ^ 2
```

or a direct contradiction form:

```lean
∀ {a b c d : ℤ},
  c ^ 2 + d ^ 2 = 2 * b ^ 2 →
  b ^ 2 + a ^ 2 = 2 * d ^ 2 →
  ¬ (a ^ 2 ≠ b ^ 2 ∨ b ^ 2 ≠ c ^ 2 ∨ c ^ 2 ≠ d ^ 2)
```

If the existing theorem only handles primitive centered APs, it is not the ideal downstream interface. Wrap it once into the midpoint theorem above.

## Suspicious/stale/too-weak points for this task

1. `Even m` in `DividedMEvenFactorsUnitStatement` is redundant after `DividedSqBranchMEvenFactors m n` has been produced. It is not false, just unnecessary for the unit proof.

2. Any AP theorem that concludes equality of the variables themselves, e.g. `a=b`, without positivity/sign hypotheses is too strong. The safe core conclusion is equality of squares. In this divided branch, factor positivity can then turn square equality into variable equality if needed, but the unit proof only needs `a^2=1`.

3. Any AP theorem requiring primitive hypotheses on `a,b,c,d` is too low-level for this branch. The branch naturally gives coprimality of `m,n`, not an immediately convenient primitive AP package for `a,b,c,d`. The wrapper should absorb primitive normalization internally.

4. The MOdd contradiction should not be routed through the four-squares AP theorem. It is strictly shorter as the mod-4 lemma `no_oddC_three_square_sum` after deriving `a^2+c^2=3*b^2` with `c` odd.

5. If there is a theorem in `N12FourSquaresAP.lean` phrased only over `ℕ`, it is usable but stale for this file: add an integer wrapper rather than pushing casts through the divided branch.
