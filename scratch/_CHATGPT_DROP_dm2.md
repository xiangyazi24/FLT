# Q228: EDS / Somos relation search and derivation for Mathlib division polynomials

## Short verdict

Mathlib **does have the general Somos / EDS relation as a definition**:

```lean
def IsEllSequence (W : ℤ → R) : Prop :=
  ∀ m n r : ℤ,
    W (m + n) * W (m - n) * W r ^ 2 =
      W (m + r) * W (m - r) * W n ^ 2 -
        W (n + r) * W (n - r) * W m ^ 2
```

This is exactly the desired identity

```text
W_{m+n} W_{m-n} W_r²
  = W_{m+r} W_{m-r} W_n² − W_{n+r} W_{n-r} W_m².
```

But Mathlib **does not currently prove** that the canonical normalized sequence

```lean
normEDS b c d : ℤ → R
```

satisfies `IsEllSequence`. The file itself lists this as TODO:

```text
TODO: prove that `normEDS` satisfies `IsEllDivSequence`.
```

So there is no theorem such as

```lean
normEDS_isEllSequence
normEDS_isEllDivSequence
preNormEDS_isEllSequence
WeierstrassCurve.ψ_isEllSequence
WeierstrassCurve.preΨ_isEllSequence
```

in current Mathlib.

What Mathlib **does have** are the defining even/odd recurrences:

```lean
preNormEDS'_even
preNormEDS'_odd
preNormEDS_even
preNormEDS_odd
normEDS_even
normEDS_odd
WeierstrassCurve.preΨ'_even
WeierstrassCurve.preΨ'_odd
WeierstrassCurve.preΨ_even
WeierstrassCurve.preΨ_odd
```

For the adjacent differential-addition case, the needed Somos instance is exactly the `r = 1`, `m = a`, `n = b` specialization with adjacent indices, and it is already present as `normEDS_odd` / `preΨ_odd` after the normalization factors are accounted for. Therefore the immediate adjacent identity should be proved from `W.preΨ_odd`; the fully general EDS relation remains a deeper missing theorem.

---

## Exact declarations found in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`

```lean
import Mathlib

noncomputable section

open Polynomial

universe u

variable {R : Type u} [CommRing R]

/-- Already in Mathlib: the general elliptic/Somos relation, as a Prop. -/
#check IsEllSequence

/-- Already in Mathlib: divisibility-sequence predicate. -/
#check IsDivSequence

/-- Already in Mathlib: conjunction of the two predicates. -/
#check IsEllDivSequence

/-- Already in Mathlib: identity sequence is elliptic. -/
#check isEllSequence_id
#check isDivSequence_id
#check isEllDivSequence_id

/-- Already in Mathlib: scalar multiples preserve the predicates. -/
#check IsEllSequence.smul
#check IsDivSequence.smul
#check IsEllDivSequence.smul

/-- Already in Mathlib: auxiliary normalized EDS and its even/odd recurrences. -/
#check preNormEDS'
#check preNormEDS'_even
#check preNormEDS'_odd
#check preNormEDS
#check preNormEDS_even
#check preNormEDS_odd

/-- Already in Mathlib: normalized EDS and its even/odd recurrences. -/
#check normEDS
#check normEDS_even
#check normEDS_odd

/-- Already in Mathlib: complement sequence/divisibility infrastructure. -/
#check complEDS₂
#check preNormEDS_mul_complEDS₂
#check normEDS_mul_complEDS₂
#check normEDS_dvd_normEDS_two_mul
#check complEDS₂_mul_b
#check complEDS'
#check complEDS'_even
#check complEDS'_odd
#check complEDS
#check complEDS_even
#check complEDS_odd

/-- Already in Mathlib: recursion principles for proving properties by the defining recurrence. -/
#check normEDSRec'
#check normEDSRec
#check complEDSRec'
#check complEDSRec

/-- Already in Mathlib: map compatibility. -/
#check map_preNormEDS'
#check map_preNormEDS
#check map_complEDS₂
#check map_normEDS
#check map_complEDS'
#check map_complEDS
```

Expected missing checks:

```lean
-- These names are intentionally commented out: they are not in current Mathlib.
-- #check normEDS_isEllSequence
-- #check normEDS_isEllDivSequence
-- #check preNormEDS_isEllSequence
-- #check WeierstrassCurve.preΨ_isEllSequence
-- #check WeierstrassCurve.ψ_isEllSequence
```

---

## If you already have an abstract `IsEllSequence` hypothesis

If somewhere in your development you have

```lean
hW : IsEllSequence W
```

then the desired relation is literally:

```lean
example {R : Type u} [CommRing R] {W : ℤ → R}
    (hW : IsEllSequence W) (i j k : ℤ) :
    W (i + j) * W (i - j) * W k ^ 2 =
      W (i + k) * W (i - k) * W j ^ 2 -
        W (j + k) * W (j - k) * W i ^ 2 := by
  exact hW i j k
```

The adjacent specialization used in differential addition is obtained by taking

```text
i = m + 1,   j = m,   k = 1.
```

Then `i+j = 2m+1`, `i-j = 1`, and `W 1 = 1` for a normalized EDS, so it becomes

```text
W(2m+1)
= W(m+2) W(m)^3 − W(m+1) W(m−1) W(m+1)^2
= W(m+2) W(m)^3 − W(m−1) W(m+1)^3.
```

This is exactly `normEDS_odd`.

```lean
example {R : Type u} [CommRing R]
    (b c d : R) (m : ℤ) :
    normEDS b c d (2 * m + 1) =
      normEDS b c d (m + 2) * normEDS b c d m ^ 3 -
        normEDS b c d (m - 1) * normEDS b c d (m + 1) ^ 3 := by
  exact normEDS_odd b c d m
```

---

## Specialization to `WeierstrassCurve.preΨ`

For Mathlib's univariate reduced/auxiliary division polynomial sequence,

```lean
W.preΨ : ℤ → R[X]
```

there is no theorem saying it is an abstract `IsEllSequence`. Instead Mathlib provides the parity-normalized recurrences directly:

```lean
WeierstrassCurve.preΨ_even
WeierstrassCurve.preΨ_odd
```

The adjacent Somos relation for `preΨ` is precisely `preΨ_odd`.

```lean
import Mathlib

noncomputable section

open Polynomial
open WeierstrassCurve

namespace WeierstrassCurve

universe u

variable {R : Type u} [CommRing R]
variable (W : WeierstrassCurve R)

/--
Adjacent Somos relation for Mathlib's reduced univariate auxiliary sequence `preΨ`.

This is exactly `W.preΨ_odd m`.  The factors of `Ψ₂Sq²` are the normalization correction between
`preΨ` and the full normalized EDS/`ψ` sequence.
-/
theorem preΨ_adjacent_somos (m : ℤ) :
    W.preΨ (2 * m + 1) =
      W.preΨ (m + 2) * W.preΨ m ^ 3 *
          (if Even m then W.Ψ₂Sq ^ 2 else 1) -
        W.preΨ (m - 1) * W.preΨ (m + 1) ^ 3 *
          (if Even m then 1 else W.Ψ₂Sq ^ 2) := by
  exact W.preΨ_odd m

/--
Even duplication recurrence for `preΨ`, also already in Mathlib.
-/
theorem preΨ_even_somos_like (m : ℤ) :
    W.preΨ (2 * m) =
      W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2) -
        W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2 := by
  exact W.preΨ_even m

end WeierstrassCurve
```

This is the lemma to use inside the raw/Kummer adjacent differential-addition identity. In particular, if the coordinate-ring calculation needs the expression

```lean
W.preΨ (m + 2) * W.preΨ m ^ 3 * correction
  - W.preΨ (m - 1) * W.preΨ (m + 1) ^ 3 * correction
```

then rewrite it with

```lean
rw [← W.preΨ_adjacent_somos m]
```

or simply

```lean
rw [← W.preΨ_odd m]
```

after arranging the sides.

---

## Specialization to the full `ψ` / `Ψ` sequence

For the full bivariate division polynomial sequence, what you really want in the coordinate ring is a theorem of this shape:

```lean
namespace WeierstrassCurve

open Polynomial
open scoped Polynomial.Bivariate

universe u

variable {R : Type u} [CommRing R]
variable (W : WeierstrassCurve R)

namespace Affine.CoordinateRing

/--
MISSING-MATHLIB-API.

The bivariate division-polynomial sequence satisfies the general EDS/Somos relation in the affine
coordinate ring.
-/
theorem mk_ψ_isEllSequence :
    IsEllSequence (fun n : ℤ => mk W (W.ψ n)) := by
  -- This is not currently exposed by Mathlib.
  -- It should follow once `normEDS_isEllSequence` is proved and `W.ψ` is connected to `normEDS`,
  -- or by direct induction using the `normEDSRec` recursion principle.
  sorry

/-- The immediately usable relation after `mk_ψ_isEllSequence`. -/
theorem mk_ψ_somos
    (i j k : ℤ) :
    mk W (W.ψ (i + j)) * mk W (W.ψ (i - j)) * mk W (W.ψ k) ^ 2 =
      mk W (W.ψ (i + k)) * mk W (W.ψ (i - k)) * mk W (W.ψ j) ^ 2 -
        mk W (W.ψ (j + k)) * mk W (W.ψ (j - k)) * mk W (W.ψ i) ^ 2 := by
  exact (mk_ψ_isEllSequence (W := W)) i j k

/-- Adjacent specialization for differential addition. -/
theorem mk_ψ_adjacent_somos
    (m : ℤ) :
    mk W (W.ψ (2 * m + 1)) =
      mk W (W.ψ (m + 2)) * mk W (W.ψ m) ^ 3 -
        mk W (W.ψ (m - 1)) * mk W (W.ψ (m + 1)) ^ 3 := by
  have h := mk_ψ_somos (W := W) (m + 1) m 1
  -- Normalize `ψ_1 = 1`, arithmetic, and multiplication order.
  -- Expected proof:
  --   simpa [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc,
  --          sub_eq_add_neg, two_mul] using h
  sorry

end Affine.CoordinateRing
end WeierstrassCurve
```

This is the exact missing coordinate-ring theorem for the bivariate route. The univariate `preΨ_odd` relation is already available, but the bivariate `ψ` relation in the coordinate ring is not exposed as a general `IsEllSequence` theorem.

---

## If you really need the fully general theorem

The clean theorem to add to `EllipticDivisibilitySequence.lean` is:

```lean
/--
MISSING-MATHLIB-API.
The canonical normalized EDS satisfies the elliptic/Somos relation.
-/
theorem normEDS_isEllSequence
    {R : Type u} [CommRing R] (b c d : R) :
    IsEllSequence (normEDS b c d) := by
  -- Substantial proof.
  -- The file currently marks this as TODO.
  sorry
```

Then the general relation becomes:

```lean
theorem normEDS_somos
    {R : Type u} [CommRing R] (b c d : R) (i j k : ℤ) :
    normEDS b c d (i + j) * normEDS b c d (i - j) * normEDS b c d k ^ 2 =
      normEDS b c d (i + k) * normEDS b c d (i - k) * normEDS b c d j ^ 2 -
        normEDS b c d (j + k) * normEDS b c d (j - k) * normEDS b c d i ^ 2 := by
  exact normEDS_isEllSequence b c d i j k
```

### Is `normEDS_isEllSequence` just `ring` after expanding `normEDS_even/odd`?

No, not globally. The recurrences `normEDS_even` and `normEDS_odd` are **two special Somos recurrences** used to define/compute the sequence. The full three-index identity for arbitrary `i j k` is a deeper consistency theorem for the normalized EDS. It would normally be proved by a strong induction using `normEDSRec`, reducing arbitrary triples to the defining even/odd recurrences. That is a real proof, not a single `ring` call.

### Is the adjacent instance a `ring` proof from `preΨ_even/odd`?

Yes, for the adjacent differential-addition case you should not prove the full theorem. Use the already-existing recurrence:

```lean
W.preΨ_odd m
```

That is exactly the `i=m+1, j=m, k=1` Somos relation after accounting for the `preΨ` normalization. Any remaining algebra in the Kummer differential-addition formula is `ring`/`ring_nf` after rewriting by `W.preΨ_odd m`, `W.Φ`, and `W.ΨSq`.

---

## Recommended implementation path

1. For the immediate adjacent differential-addition identity, use:

```lean
rw [W.preΨ_odd m]
```

or the wrapper:

```lean
rw [W.preΨ_adjacent_somos m]
```

2. Do **not** attempt to prove the full `normEDS_isEllSequence` unless you need arbitrary `i,j,k`.

3. If you need the bivariate coordinate-ring route, add the missing theorem:

```lean
Affine.CoordinateRing.mk_ψ_isEllSequence
```

and derive:

```lean
Affine.CoordinateRing.mk_ψ_adjacent_somos
```

4. For the x-only raw polynomial proof, the relevant Somos content is already available through:

```lean
WeierstrassCurve.preΨ_odd
WeierstrassCurve.preΨ_even
```

The remaining failures are formula orientation, parity normalization, or `b`-relation issues, not lack of the adjacent EDS recurrence.
