# SEAM2 char-conditions discharge — design (scoped 2026-06-24, while SEAM1 bridges grind)

## The three sorries (Torsion.lean L85-87, in `nsmul_eq_zero_iff_ΨSq_eval`, namespace KeystoneNTorsion)
- `h4  : (4 : k) ≠ 0`
- `hψ_ne : ∀ m : ℤ, m ≠ 0 → W.ψ m ≠ 0`
- `hc3 : W.Ψ₃ ≠ 0`

## Finding (verified, read-only)
- `k` in namespace KeystoneNTorsion is a BARE `[Field k] [DecidableEq k]` — NO char hypothesis.
- Over a general field these are FALSE in small char (char 2 ⇒ 4 = 0; char 3 ⇒ Ψ₃ leading 3·X⁴ degenerates).
- BOTH keystone proofs require them as explicit args:
  - `scratch/KeystoneEDS.lean:392  nsmul_eq_zero_iff_ΨSq_eval (W) [IsElliptic] (h4)(hψ_ne)(hc3) …`
  - `KeystoneLadder.nsmul_eq_zero_iff_ΨSq_eval … h4 hψ_ne hc3` (the one Torsion L88 calls)
  So a re-route (à la SEAM1 wiring) does NOT avoid them — they are genuine math hypotheses of the
  diff-add ladder, not cosmetic. (Hypothesis "route to the proven keystone to kill them for free" = REJECTED.)

## Sound discharge = thread char-0 from the Mazur instantiation
- Consumer chain: L88 keystone → L630 `KeystoneNTorsion.nTorsion_card_eq` → n-torsion cardinality → Mazur.
- Mazur statement is over a NUMBER FIELD ⇒ char 0 ⇒ all three hold:
  - `h4`: `4 ≠ 0` from `[CharZero k]` (`by norm_num` / `Nat.cast_ne_zero`).
  - `hc3`: `Ψ₃ = 3X⁴+b₂X³+3b₄X²+3b₆X+b₈`; in char 0 leading coeff `3 ≠ 0` ⇒ `Ψ₃ ≠ 0` (degree ≥ 4 ≠ ⊥).
  - `hψ_ne`: division poly `ψ m ≠ 0` for `m ≠ 0` over char-0 elliptic curve — standard; check Mathlib
    `WeierstrassCurve.ψ`/`preΨ`/`Ψ` nonvanishing lemmas (likely via `natDegree`/leading-coeff, or an
    existing `ψ_ne_zero`-type lemma; grep Mathlib DivisionPolynomial for nonvanishing first).

## Plan (land AFTER sub-agent A returns — same-file region as A's preΨ' wiring, do not race)
1. Add `[CharZero k]` (or a weaker `(hchar : (2:k) ≠ 0 ∧ (3:k) ≠ 0)` if CharZero is too strong for the
   intended generality) to the KeystoneNTorsion theorems that need it — minimal set: the three theorems
   in the L83-127 block + any keystone caller. This is a SIGNATURE change → ripples to L630 caller and up
   to the Mazur instantiation (which supplies CharZero from NumberField). Confirm the Mazur site provides it.
2. Discharge h4/hc3 by `norm_num`/degree; hψ_ne by the Mathlib nonvanishing lemma (or a small
   leading-coeff argument). 0 axioms, named sorry only if a Mathlib gap is hit.
3. NOTE: signature/structure change — per "版本的事情你不管", the CharZero threading is mathematically
   necessary (statements false otherwise), NOT a convention rename. Record in CHANGELOG; if the generality
   (CharZero vs explicit 2,3 ≠ 0) is a judgement call affecting the paper's stated generality, surface to Xiang.
