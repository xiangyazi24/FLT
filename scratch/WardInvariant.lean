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

/-- **Full single-index invariant.** Over a domain where the `normEDS` values do not vanish
(e.g. the division-polynomial setting — `preΨ` nonvanishing via Mathlib's degree lemmas),
`InvarRel n` holds for every `n`. Proof: `Int` induction off the base cases and `invarRel_step_mul`,
cancelling `D_n ≠ 0`; negative `n` by the `Nseq`/`Dseq` sign symmetry. -/
lemma invarRel_all [IsDomain R] (b c d : R)
    (hne : ∀ k : ℤ, k ≠ 0 → normEDS b c d k ≠ 0) (n : ℤ) : InvarRel b c d n := by
  have hge2 : ∀ m : ℤ, 2 ≤ m → InvarRel b c d m := by
    intro m hm
    induction m, hm using Int.le_induction with
    | base => exact invarRel_two b c d
    | succ k hk ih =>
      have hstep := invarRel_step_mul b c d k ih
      have hDk : Dseq b c d k ≠ 0 := by
        unfold Dseq
        exact mul_ne_zero (mul_ne_zero (hne (k+1) (by omega)) (hne k (by omega)))
          (hne (k-1) (by omega))
      unfold InvarRel
      have := (mul_eq_zero.mp hstep).resolve_left hDk
      linear_combination this
  have hpos : ∀ m : ℤ, 0 ≤ m → InvarRel b c d m := by
    intro m hm
    rcases lt_or_ge m 2 with h2 | h2
    · interval_cases m
      · exact invarRel_zero b c d
      · exact invarRel_one b c d
    · exact hge2 m h2
  rcases lt_or_ge n 0 with h | h
  · have hsym : InvarRel b c d (-n) := hpos (-n) (by omega)
    have hN : Nseq b c d (-n) = - Nseq b c d n := by
      unfold Nseq
      rw [show -n+2 = -(n-2) by ring, show -n-1 = -(n+1) by ring, show -n+1 = -(n-1) by ring,
        show -n-2 = -(n+2) by ring, normEDS_neg, normEDS_neg, normEDS_neg, normEDS_neg, normEDS_neg]
      ring
    have hD : Dseq b c d (-n) = - Dseq b c d n := by
      unfold Dseq
      rw [show -n+1 = -(n-1) by ring, show -n-1 = -(n+1) by ring, normEDS_neg, normEDS_neg, normEDS_neg]
      ring
    unfold InvarRel at hsym ⊢
    rw [hN, hD] at hsym
    linear_combination -hsym
  · exact hpos n h

/-- **Double-off relation** `N_k D_m = N_m D_k` (i.e. `T_{k,m} = 0`): the conserved ratio is
index-independent. From `invarRel_all` (`c N = (d+b⁴) D`) by cancelling `c`. -/
lemma Trel_zero [IsDomain R] (b c d : R) (hc : c ≠ 0)
    (hne : ∀ k : ℤ, k ≠ 0 → normEDS b c d k ≠ 0) (k m : ℤ) :
    Nseq b c d k * Dseq b c d m = Nseq b c d m * Dseq b c d k := by
  have hk := invarRel_all b c d hne k
  have hm := invarRel_all b c d hne m
  unfold InvarRel at hk hm
  have hcT : c * (Nseq b c d k * Dseq b c d m - Nseq b c d m * Dseq b c d k) = 0 := by
    linear_combination Dseq b c d m * hk - Dseq b c d k * hm
  have := (mul_eq_zero.mp hcT).resolve_left hc
  linear_combination this

end FLT.EDS
