import scratch.WardConservation

/-!
# Single-index invariant for `normEDS`  (Ward / van der Poorten–Swart conserved quantity)

`c · N_n = (d + b⁴) · D_n` for all `n`, where `N_n`, `D_n` are `Nseq`, `Dseq` (the Somos-4
numerator / denominator). Equivalently `N_n / D_n` is the index-independent conserved quantity
`λ = (d+b⁴)/c` — this is the `s = 1` case of the general-`s` invariant
(`invarNum s n / invarDenom s n` in Mathlib PR #13155, alreadydone; van der Poorten–Swart Thm 3).

**Scope note (deliberate, see WARD_FULL_DOCTRINE.md):** we prove only the `s = 1` invariant, which
is exactly what the `AddRel`/`OffRel` gap induction needs to reach the *fully general*
`IsEllSequence (normEDS)`. The general-`s` form (PR #13155) is intermediate-lemma generality, not a
stronger theorem; if a future need arises it can be generalized here. Source of the approach:
van der Poorten–Swart Theorem 3; cf. Mathlib PR #13155 (alreadydone / Junyan Xu). The code is ours.

Proof: it is a polynomial identity in `(b,c,d)`, proved over the universal domain (where `D_n` is a
non-zero-divisor for `n ≥ 2`) by induction off the conserved ratio (`normEDS_conservation`), then it
holds over every `CommRing` since both sides are the same `(b,c,d)`-polynomial.
-/

namespace FLT.EDS

variable {R : Type*} [CommRing R]

/-- The `s = 1` invariant relation `c · N_n = (d + b⁴) · D_n`. -/
def InvarRel (b c d : R) (n : ℤ) : Prop :=
  c * Nseq b c d n = (d + b ^ 4) * Dseq b c d n

/-- Base cases: `n = 0, 1` (both sides vanish) and `n = 2`. -/
lemma invarRel_zero (b c d : R) : InvarRel b c d 0 := by
  unfold InvarRel Nseq Dseq
  simp [normEDS_zero, normEDS_one, normEDS_two, normEDS_neg]

lemma invarRel_one (b c d : R) : InvarRel b c d 1 := by
  unfold InvarRel Nseq Dseq
  simp [normEDS_zero, normEDS_one, normEDS_two, normEDS_three, normEDS_neg]

lemma invarRel_two (b c d : R) : InvarRel b c d 2 := by
  unfold InvarRel Nseq Dseq
  norm_num [normEDS_zero, normEDS_one, normEDS_two, normEDS_three, normEDS_four]
  ring

/-- Inductive step (multiplied form, holds over any `CommRing`): from `InvarRel n`,
`D_n · (InvarRel n+1)` vanishes. Cofactors `c · conservation + D_{n+1} · (IH)`, an atom-level ring
identity (no unfolding of `Nseq`/`Dseq` needed). The final `InvarRel (n+1)` is got by cancelling
`D_n` over a domain where `D_n ≠ 0` (e.g. the division-polynomial setting, `preΨ` nonvanishing via
`Mathlib …DivisionPolynomial.Degree`). -/
lemma invarRel_step_mul (b c d : R) (n : ℤ) (hn : InvarRel b c d n) :
    Dseq b c d n * (c * Nseq b c d (n+1) - (d + b ^ 4) * Dseq b c d (n+1)) = 0 := by
  have hcons := normEDS_conservation b c d n
  unfold InvarRel at hn
  linear_combination c * hcons + Dseq b c d (n+1) * hn

end FLT.EDS
