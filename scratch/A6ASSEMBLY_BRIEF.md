# A6 ASSEMBLY (v2, audit-keyed) — torsion finiteness via projective x-height → drop mordell_weil_fg

Repo ~/repos/flt-ai, branch ai-scratch, ON uisai2. Build with `lake build`/`lake env lean` here
(incremental; Mathlib cached; NEVER local mini build; do NOT edit core/built files). Work in a NEW
file scratch/A6TorsionFinite.lean. Do NOT edit TorsionFinite.lean / Torsion.lean / any built file yet.

## READ FIRST — the de-risked blueprint
**scratch/A6_R8_Adversarial_FULL.md is the AUTHORITATIVE implementation guide.** Follow its
Section 4 wiring and Section 2/3/5 lemma signatures. Do not improvise an alternative architecture.

## TARGET (exact signature from FLT/Assumptions/MazurProof/TorsionFinite.lean)
```
theorem rational_torsion_finite_height (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion (E⧸ℚ).Point : Set (E⧸ℚ).Point).Finite
```
(Later we rewire the alias to this and DELETE the axiom. NOT this task — build the proof here.)

## CRITICAL RECONCILIATION — raw vs projective height (the audit's point 4)
The proven lemma in A6HeightProto.lean, `dup_projective_height_lower_height_api_seam`, is on the
RAW pair height `naiveLogHeightP1Q (X Z : ℚ) = log max|X| |Z|`:
   ∃ C0, ∀ X Z:ℚ, (X,Z)≠0 → naiveLogHeightP1Q (dupNumH W X Z)(dupDenH W X Z) ≥ 4·naiveLogHeightP1Q X Z − C0.
But Northcott + finiteness need the TRUE PROJECTIVE height on PRIMITIVE integer reps (audit §1: P1Q,
P1Q.logHeight). At 2-torsion the output [F:0] has primitive height 0, NOT log|F|. So you must BRIDGE:

1. Define `P1Q` (primitive coprime ℤ rep, audit §1) and `P1Q.logHeight`. For a primitive [X:Z]:
   `naiveLogHeightP1Q (X:ℚ)(Z:ℚ) = P1Q.logHeight ⟨X,Z,…⟩` (equal because primitive).
2. **gcd bridge** (audit §3 `dup_gcd_dvd_resultant`, MUST cover G=0): for primitive [X:Z],
   gcd(dupNumH X Z, dupDenH X Z) ∣ Δ²  (extract from `dup_bezout_affine` already in A6HeightProto;
   common divisor divides R·X⁷ and R·Z⁷, gcd(X,Z)=1 ⇒ divides R=Δ²; gcd(F,0)=|F|∣Δ²).
3. Hence the TRUE projective doubling bound:
   `P1Q.logHeight (normalize (dupNumH X Z)(dupDenH X Z)) = naiveLogHeightP1Q(F,G) − log gcd
     ≥ [4·P1Q.logHeight x − C0] − log|Δ²|`. Set C := C0 + 2 log|Δ|.
REUSE the proven raw lemma — do NOT re-prove the lower bound from scratch. The compactness proof is
already done; you are only adding the gcd reduction on top of it.

## THE CHAIN (audit §4 wiring — build exactly this)
- `xRep_two_nsmul_same_dup` (audit §2.A / §5.2): x(2•P) = projective [dupNumH(xP):dupDenH(xP)] for
  P:(E⧸ℚ).Point. Full Lean is in scratch/A6_R5_EC_Duplication_FULL.md (SameP1 version) — adapt to P1Q.Same.
  Handle P=0, 2•P=0, vertical-tangent cases (R5 already splits them).
- `xHeight E P := P1Q.logHeight (xRep E P)`; `xHeight_double_lower : ∃ C≥0, ∀P, xHeight(2•P) ≥ 4·xHeight P − C`
  (from the bridge above + the dup formula).
- `Northcott.comp_of_finite_fibers` (audit §2.C — full proof given; NOT in Mathlib, write it).
- `P1Q.logHeight_northcott` via `P1Q.mulHeight_northcott_nat` (audit §2.D — integer box first, robust route).
- `xRep_finite_fibers` (audit §5.3): each P1Q value has ≤2 points (∞ singleton; affine ≤2 y-values).
- `xHeight_northcott := comp_of_finite_fibers xRep logHeight_northcott xRep_finite_fibers`.
- `finite_torsion_of_northcott_double_lower` (audit §5.5, LOW risk): orbit-max argument — torsion P has
  finite {2ᵏ•P}; if xHeight(P) > C/3 then xHeight strictly grows along the orbit, unbounded,
  contradiction; so all torsion bounded by C/3; Northcott ⇒ finite set of x-values; ≤2 pts each ⇒ finite.
  Uses only AddCommGroup.torsion + Finset.max'/max'_le_iff.
- `rational_torsion_finite_height E : (AddCommGroup.torsion …).Finite` := wrap the above + Set.toFinite.

## RULES (campaign-critical)
- NO axiom-escape, NO `theorem := sorry` hiding an axiom. Push EVERY step. The arithmetic/order pieces
  (gcd∣Δ² incl. G=0, the orbit inequality, ≤2-pts-per-x, the integer-box Northcott) are ALL fully closeable.
  If a genuinely-missing Mathlib API blocks one sub-step (e.g. a specific Projectivization/height lemma),
  isolate it as ONE clearly-NAMED `sorry` seam and report EXACTLY which API is missing — do not stop.
- Reuse A6HeightProto's proven lemmas; import it. Don't re-prove resultant=Δ² or the raw lower bound.
- Report: which of {gcd-bridge, xRep_two_nsmul_same_dup, logHeight_northcott, xRep_finite_fibers,
  orbit-lemma, top theorem} are CLOSED (0 sorry) vs precise residual named seams + missing API each needs.
  Run `lake env lean scratch/A6TorsionFinite.lean`, paste exit code + `grep -n "sorry\|axiom"` output.
- Unbounded grind. Only legitimate stop: math wrong, or a named-and-reported missing Mathlib API.
