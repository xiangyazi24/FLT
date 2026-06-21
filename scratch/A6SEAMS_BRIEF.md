# A6 FINAL — close the 2 residual seams in A6TorsionFinite.lean

Repo ~/repos/flt-ai, branch ai-scratch, ON uisai2. Build with `lake build`/`lake env lean` here
(incremental; NEVER local mini build; do NOT edit core/built files outside the scratch target).

## STATE (verified)
scratch/A6TorsionFinite.lean compiles (EXIT 0) but has EXACTLY 2 named `sorry` seams (0 axioms).
Everything else (R7 ℙ¹(ℚ) Northcott, finite fibers, orbit/telescoping) is CLOSED. The 2 seams:

1. **L~191 `xRep_two_nsmul_same_dup`** — projective EC duplication formula:
   P1Q.SameQ (xRep E (2•P)) (dupNumH E xX xZ) (dupDenH E xX xZ).
   CLOSE IT using scratch/A6_R5_EC_Duplication_FULL.md — it has the FULL proof of the SameP1 version
   `xRep_two_nsmul_same_dup_affine` (case split 0 / 2-torsion / tangent, with explicit
   linear_combination certificates). Adapt SameP1 → P1Q.SameQ and pass from the raw point vector
   [x:1] to the primitive integer rep [num:den] via degree-4 homogeneity.

2. **L~206 `dup_projective_height_lower_from_raw_gcd`** — the raw→true height gcd bridge:
   from the PROVEN raw lemma `dup_projective_height_lower_height_api_seam` (in A6HeightProto.lean) plus
   gcd(F,G)∣Δ², conclude P1Q.logHeight y ≥ 4·P1Q.logHeight x − C.
   CLOSE IT using scratch/GITDROP_dm1_gcd_bridge.md — it has the gcd∣Δ² proof:
   `HomogeneousBezoutCertificate`, `gcd_dvd_D_natAbs_of_natAbs_coprime` (gcd(F,G)∣Δ² via the two
   homogeneous Bezout identities Δ²X⁷=Ux·F+Vx·G, Δ²Z⁷=Uz·F+Vz·G + gcd(X⁷,Z⁷)=1), INCLUDING the G=0
   degenerate case (Nat.gcd|F|0=|F|∣Δ²). It has 2 minor API-wrapper sorries (IsCoprime→Nat.Coprime,
   gcd_mul_left naming) — RESOLVE those by building. You must also produce the actual homogeneous
   Bezout certificate for THIS curve's dupNumH/dupDenH (the two identities with explicit deg-3
   cofactors), checkable by ring; the resultant=Δ² fact is already proven in A6HeightProto.lean.

## RULES (campaign-critical — the previous codex MISREPORTED closure; do not repeat)
- NO axiom-escape, NO `theorem := sorry`. Push every step.
- After finishing, you MUST run `grep -n "sorry\|admit\|axiom" scratch/A6TorsionFinite.lean` and
  `lake env lean scratch/A6TorsionFinite.lean`, and PASTE BOTH OUTPUTS VERBATIM in your report. Do
  NOT claim a seam is closed unless the grep shows it is gone. State the EXACT remaining sorry count.
- If one seam closes and the other needs a genuinely-missing Mathlib API, report precisely which API
  and leave that ONE seam as a clearly-named sorry — but the EC dup formula (R5 code exists) and the
  gcd bridge (dm1 code exists) are both closeable; grind them.
- Only edit scratch/A6TorsionFinite.lean (+ scratch/A6HeightProto.lean if you must expose a helper).
  Do NOT touch TorsionFinite.lean / Torsion.lean / built files.
- Unbounded grind. Only legitimate stop: math wrong, or named-and-reported missing Mathlib API.
