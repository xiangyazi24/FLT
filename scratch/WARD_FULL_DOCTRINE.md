# DOCTRINE — prove IsEllSequence (normEDS b c d)  [the open Mathlib TODO]

## Goal
`∀ m n r : ℤ, W(m+n)W(m-n)W(r)² = W(m+r)W(m-r)W(n)² − W(n+r)W(n-r)W(m)²` for W = normEDS b c d,
any CommRing R. Unlocks the keystone EDS-core doubling + addition → nsmul_eq_zero_iff_ΨSq_eval.

## What is PROVEN (base, 0 axioms)
- `normEDS_adjacent_somos` = E(m,2,1) for all m (since W(1)=1,W(2)=b,W(3)=c). The induction BASE CASE.
- Universal-ring + map_normEDS transport machinery (reusable for the whole proof).
- complEDS machinery (Mathlib) handles the IsDivSequence half; IsEllSequence is the hard half.

## CAS-established NEGATIVE results (rule out the easy routes)
- E(m,n,1) for n≥3 is NOT in the ideal of adjacent Somos at any finite radius (r≤4), EVEN with the
  curve relation incorporated AND even after denominator-clearing by W(m±1). The EDS satisfies GLOBAL
  relations beyond any local Somos set — Ward's theorem is not a finite cofactor certificate.
- Therefore: NO local Gröbner/linear_combination proof. Needs a genuine induction using the DEFINING
  recurrence (normEDS_even/odd from base values), and the double-index W(m±n) makes it a 2-index problem.

## Candidate avenues (ranked, to refine with ChatGPT rounds)
(a) **r=1 reduction + induction on n.** First prove E(m,n,1) ∀m,n (the "addition formula"); then reduce
    general E(m,n,r) to r=1 by a transfer/symmetry. Induction on n via the recurrence; the step must
    handle W(m±n) for symbolic m (the crux).
(b) **Elliptic-net / Stange framework.** E is the 1-dim elliptic net relation; Stange's recurrence gives
    a clean 2D induction. Possibly the most formalization-friendly (explicit recurrence).
(c) **Universal-ring + σ-function transport.** Prove over MvPolynomial ℤ (domain), via the Weierstrass-σ
    3-term identity pulled back algebraically. Likely needs analytic σ — probably NOT Lean-friendly.
(d) **complEDS-based.** Leverage Mathlib's complement-sequence identities (complEDS_even/odd) — check if
    they shorten the E-relation, not just divisibility.

## Method note (Xiang 2026-06-22)
Hard theorem → DRIVE myself first + go several ROUNDS with ChatGPT (parallel, verify-don't-transcribe).
This is the right ChatGPT use (not the serial-wait anti-pattern of lesson-0067). Year-long horizon, 遇山开山.

## Terminal condition
`IsEllSequence (normEDS b c d)` proven, 0 custom axioms, #print axioms standard-only.
