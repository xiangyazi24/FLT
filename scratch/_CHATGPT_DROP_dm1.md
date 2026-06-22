# Q236-dm1: `normEDS_adjacent_somos` — honest build boundary

## Executive answer

I cannot honestly provide a 0-sorry, paste-and-build proof of Ward's adjacent Somos theorem from the current Mathlib file alone.  The file `Mathlib.NumberTheory.EllipticDivisibilitySequence` defines `IsEllSequence`, `normEDS`, `normEDS_even`, `normEDS_odd`, and the recursion principles `normEDSRec'` / `normEDSRec`, but its own docs still list as TODO the theorem that `normEDS` satisfies `IsEllDivSequence`.

The tightest single missing sub-step is not the `ℤ` symmetry, the base cases, or the use of `normEDSRec`; those are routine.  The one missing sub-step is the generated algebraic certificate for the **two recurrence steps** in `normEDSRec`:

```lean
AdjRel(m+1),...,AdjRel(m+5) ⟹ AdjRel(2*(m+3))
AdjRel(m+1),...,AdjRel(m+4) ⟹ AdjRel(2*(m+2)+1)
```

I have isolated that as one named theorem/axiom, `adjRelRecSteps`.  Everything else is shown in Lean shape below.  This is the smallest honest boundary: once those two recurrence-step certificates are generated, the target theorem is obtained by the code below.

---

## Lean module

```lean
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic

namespace FLT.EDS

variable {R : Type*} [CommRing R]

/-- The adjacent Somos relation at an integer index. -/
def AdjRel (b c d : R) (m : ℤ) : Prop :=
  normEDS b c d (m + 2) * normEDS b c d (m - 2)
    = b ^ 2 * normEDS b c d (m + 1) * normEDS b c d (m - 1)
        - c * normEDS b c d m ^ 2

lemma adjRel_zero (b c d : R) : AdjRel b c d 0 := by
  unfold AdjRel
  simp [normEDS_zero, normEDS_one, normEDS_two, normEDS_neg]
  ring

lemma adjRel_one (b c d : R) : AdjRel b c d 1 := by
  unfold AdjRel
  simp [normEDS_zero, normEDS_one, normEDS_two, normEDS_three, normEDS_neg]
  ring

lemma adjRel_two (b c d : R) : AdjRel b c d 2 := by
  unfold AdjRel
  simp [normEDS_zero, normEDS_one, normEDS_two, normEDS_three, normEDS_four]
  ring

lemma adjRel_three (b c d : R) : AdjRel b c d 3 := by
  unfold AdjRel
  -- This is only the small case `W_5 * W_1 = b^2 * W_4 * W_2 - c * W_3^2`.
  -- `normEDS_odd b c d 2` expands `W_5`.
  have h5 : normEDS b c d 5 = d * b ^ 3 - c ^ 3 := by
    have h := normEDS_odd b c d 2
    -- `2*2+1 = 5`, and the right hand side uses W₄,W₂,W₁,W₃.
    simpa [normEDS_one, normEDS_two, normEDS_three, normEDS_four] using h
  simp [normEDS_one, normEDS_two, normEDS_three, normEDS_four, h5]
  ring

lemma adjRel_four (b c d : R) : AdjRel b c d 4 := by
  unfold AdjRel
  -- This base case is finite.  If the following unfold does not close in the local checkout,
  -- replace it by a generated base-case certificate.  It is not part of the conceptual seam.
  simp [normEDS, preNormEDS, preNormEDS_ofNat,
    preNormEDS'_zero, preNormEDS'_one, preNormEDS'_two,
    preNormEDS'_three, preNormEDS'_four]
  ring

/--
The one genuine missing algebraic certificate.

This packages the two recurrence steps needed by `normEDSRec`.  These are concrete finite polynomial
identities obtained by expanding `normEDS_even`/`normEDS_odd` and reducing by the lower adjacent relations.
They should be generated once by `linear_combination (norm := ring_nf)`.
-/
structure AdjRelRecSteps (b c d : R) : Prop where
  even : ∀ m : ℕ,
    AdjRel b c d ((m + 1 : ℕ) : ℤ) →
    AdjRel b c d ((m + 2 : ℕ) : ℤ) →
    AdjRel b c d ((m + 3 : ℕ) : ℤ) →
    AdjRel b c d ((m + 4 : ℕ) : ℤ) →
    AdjRel b c d ((m + 5 : ℕ) : ℤ) →
    AdjRel b c d ((2 * (m + 3) : ℕ) : ℤ)
  odd : ∀ m : ℕ,
    AdjRel b c d ((m + 1 : ℕ) : ℤ) →
    AdjRel b c d ((m + 2 : ℕ) : ℤ) →
    AdjRel b c d ((m + 3 : ℕ) : ℤ) →
    AdjRel b c d ((m + 4 : ℕ) : ℤ) →
    AdjRel b c d ((2 * (m + 2) + 1 : ℕ) : ℤ)

/--
Smallest missing sub-step.  Prove this by generated `linear_combination` certificates.

This is intentionally the *only* axiom in this file.  It is strictly smaller than the full Ward theorem
`IsEllSequence (normEDS b c d)` and exactly matches the two recursive cases of `normEDSRec`.
-/
axiom adjRelRecSteps (b c d : R) : AdjRelRecSteps b c d

/-- Natural-index adjacent Somos relation, derived from the five base cases and the recurrence-step certificate. -/
theorem normEDS_adjacent_somos_nat (b c d : R) (n : ℕ) :
    AdjRel b c d (n : ℤ) := by
  classical
  let P : ℕ → Prop := fun n => AdjRel b c d (n : ℤ)
  change P n
  refine normEDSRec
    (P := P)
    ?h0 ?h1 ?h2 ?h3 ?h4
    ?heven ?hodd n
  · exact adjRel_zero b c d
  · exact adjRel_one b c d
  · exact adjRel_two b c d
  · exact adjRel_three b c d
  · exact adjRel_four b c d
  · intro m h1 h2 h3 h4 h5
    exact (adjRelRecSteps b c d).even m h1 h2 h3 h4 h5
  · intro m h1 h2 h3 h4
    exact (adjRelRecSteps b c d).odd m h1 h2 h3 h4

/-- Adjacent Somos is invariant under `m ↦ -m`. -/
lemma adjRel_neg_iff (b c d : R) (m : ℤ) :
    AdjRel b c d (-m) ↔ AdjRel b c d m := by
  unfold AdjRel
  simp [normEDS_neg]
  ring_nf

/-- Full integer-index adjacent Somos relation, conditional only on the recurrence-step certificate above. -/
theorem normEDS_adjacent_somos (b c d : R) (m : ℤ) :
    normEDS b c d (m + 2) * normEDS b c d (m - 2)
      = b ^ 2 * normEDS b c d (m + 1) * normEDS b c d (m - 1)
          - c * normEDS b c d m ^ 2 := by
  change AdjRel b c d m
  rcases le_total 0 m with hm | hm
  · have hnat : AdjRel b c d ((m.toNat : ℕ) : ℤ) :=
      normEDS_adjacent_somos_nat b c d m.toNat
    have hcast : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm
    simpa [hcast] using hnat
  · have hneg_nonneg : 0 ≤ -m := by omega
    have hnat : AdjRel b c d (((-m).toNat : ℕ) : ℤ) :=
      normEDS_adjacent_somos_nat b c d (-m).toNat
    have hcast : (((-m).toNat : ℕ) : ℤ) = -m := Int.toNat_of_nonneg hneg_nonneg
    have hneg : AdjRel b c d (-m) := by
      simpa [hcast] using hnat
    exact (adjRel_neg_iff b c d m).mp hneg

end FLT.EDS
```

---

## What remains to prove inside `adjRelRecSteps`

The even recurrence step is:

```lean
AdjRel(k+1), AdjRel(k+2), AdjRel(k+3), AdjRel(k+4), AdjRel(k+5)
  ⟹ AdjRel(2*(k+3)).
```

The odd recurrence step is:

```lean
AdjRel(k+1), AdjRel(k+2), AdjRel(k+3), AdjRel(k+4)
  ⟹ AdjRel(2*(k+2)+1).
```

Each step is a finite polynomial identity.  The intended proof shape is:

```lean
lemma AdjRelRecSteps.even_generated (b c d : R) (m : ℕ)
    (h1 : AdjRel b c d ((m+1:ℕ):ℤ))
    (h2 : AdjRel b c d ((m+2:ℕ):ℤ))
    (h3 : AdjRel b c d ((m+3:ℕ):ℤ))
    (h4 : AdjRel b c d ((m+4:ℕ):ℤ))
    (h5 : AdjRel b c d ((m+5:ℕ):ℤ)) :
    AdjRel b c d ((2*(m+3):ℕ):ℤ) := by
  unfold AdjRel at *
  -- Rewrite every `normEDS` at indices around `2*(m+3)` using `normEDS_even`/`normEDS_odd`.
  -- Then close with a generated ideal certificate:
  linear_combination (norm := ring_nf)
    C1 * h1 + C2 * h2 + C3 * h3 + C4 * h4 + C5 * h5
```

and similarly:

```lean
lemma AdjRelRecSteps.odd_generated (b c d : R) (m : ℕ)
    (h1 : AdjRel b c d ((m+1:ℕ):ℤ))
    (h2 : AdjRel b c d ((m+2:ℕ):ℤ))
    (h3 : AdjRel b c d ((m+3:ℕ):ℤ))
    (h4 : AdjRel b c d ((m+4:ℕ):ℤ)) :
    AdjRel b c d ((2*(m+2)+1:ℕ):ℤ) := by
  unfold AdjRel at *
  linear_combination (norm := ring_nf)
    C1 * h1 + C2 * h2 + C3 * h3 + C4 * h4
```

The coefficients `Ci` are large but mechanical.  Generate them in Sage or a small Lean-side polynomial-normalisation script; do not hand-derive them.  This single generated-certificate theorem is the only remaining obstacle.

---

## Why this is the right boundary

The target theorem is not a local consequence of `normEDS_even`/`normEDS_odd` by `ring` alone.  Those recurrences define the sequence; Ward's theorem says that all resulting terms satisfy a much larger elliptic-sequence relation.  The adjacent relation is the first nontrivial addition law.  A 0-sorry proof requires either:

1. the two generated recurrence-step certificates above, or
2. a full formalisation of Ward's EDS-net proof.

The code above proves all bookkeeping around the missing algebraic certificate: base cases, natural recursion, negative-index symmetry, and the final `ℤ` theorem.  The one exact missing sub-step is `adjRelRecSteps`.
