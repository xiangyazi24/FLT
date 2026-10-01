TASK_ID: FLT-C13-B03-PLAN
REVISION: 1
TYPE: RESULT
STATUS: SOURCE-DESIGN-DELIVERED; B00/B03 OPEN
REPO: xiangyazi24/FLT
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
REQUEST_COMMIT: 4870aa5a727ab0de9c843106a0fa562210898714
SOURCE_COMMIT: a6290bc36c3549d89239da82b13b1f59ebd0388e
SOURCE_BRANCH: verify-sorry-restore
SUPERSEDES: none
NONCE: FLT-DOT-20261001

# Result

Six new, uncompiled candidate Lean files and two detailed source-design notes are supplied. This completes the requested source audit/proof-design delivery, not the mathematical B00/B03 proof. Every Lean parsing, elaboration, build, and `#print axioms` check: **NOT RUN**. No C13 axiom removal is claimed. The lead owns integration, compilation, and final axiom acceptance.

B00: the three existing degree-zero witnesses support a candidate class-level repair (not exact raw equality). The independent `Data.infinityOrder` field is not tied to its generic infinity chart. Bare reorientation therefore cannot establish coherence: degree-one nInf=1 needs correction and degree-two marking needs a genuine audit/repair. `IntegralComparison` gives concrete regular-function principal relations on both charts, a common overlap fraction, and nonzero reductions. `GlobalExistenceTarget` is only a precisely defined proposition; its existence theorem remains OPEN.

B03: source-level tensor and reduction identities support helper proofs; recentering converts additivity to the degree-four equation u(P)+u(Q)=u(P+Q)+u(0). Neither the integral comparison for a global family nor degree-four principal-relation invariance of the explicit code is proved. The nineteen-element set equivalence and degree-two AbelRel classification do not supply a geometric Picard group law. The cusp normalization check is consistent: raw codes 16, 0, 13 become 0, 3, 16 after recentering by 16. This finite check is not global additivity.

# Read in dependency order

1. [B00 audit and exact source citations](../../notes/B00-coherent-chooser-design.md). Candidate [degree-zero class repair](../candidates/N13CoherentDegreeZeroChooser.lean) includes `MazurProof.N13CoherentDegreeZeroChooser.exists_degreeZero_class_data`, `reorientData_toSpecialPic`, and the derived sign check `caLine_minus_one_class`.
2. [Concrete chart comparisons](../candidates/N13CoherentChartComparison.lean): `MazurProof.N13CoherentChartComparison.IntegralComparison`, `SpecialComparison`, `map_cleared_ideal_eq`, `IntegralComparison.reduce`. Proving generic marking coherence and representative-independent integral comparison existence remains OPEN.
3. [Chooser specification](../candidates/N13CoherentChooserSpecification.lean): `MazurProof.N13CoherentChooserSpecification.Chooser`, `HasIntegralTensorComparisons`, and `GlobalExistenceTarget`. These expose rather than discharge the existence obligation. No theorem named `exists_coherent_global_chooser` is asserted.
4. [Tensor compatibility](../candidates/N13TwoChartTensorCompatibility.lean): namespace `MazurProof.N13.TwoChartTensorCompatibility`, especially `genericClass_tensor_balance`, `restrict_tensor`, `restrict_data`, and `restrict_tensor_data`. Generic class balance does not imply whole-chart equivalence.
5. [B03 audit and exact missing bridge](research-dot-FLT-C13-B03-lane.md) gives the complete Lean target for `degreeFourCode_eq_of_comparison`, the conditional mathematical proof, source declarations, and infrastructure gaps. The target remains OPEN, not a postulate in candidate code.
6. [Recenter arithmetic](../candidates/N13SpecialCodeRecenter.lean): namespace `MazurProof.N13.SpecialCodeRecenter`, `specialCode_zero`, `specialCode_translate`, `specialCode_add_iff`, `specialCode_abel_add_iff`. These prove elementary equivalences of obligations only.
7. [Cusp consistency checks](../candidates/N13SpecialCuspCodeChecks.lean): namespace `MazurProof.N13.SpecialCuspCodeChecks`, including `pointCode_cusp` and `inverse_pair_recentered`. The sheet reversal at x=1 is essential.

All exact declarations and their source filenames are cited in the two detailed notes, exclusively at SOURCE_COMMIT (additional exact-pin reads are explicitly identified there). In particular, source `N13CoherentPointReduction.exactRaw_saturated_does_not_determine_specialClass` invalidates the tempting shortcut. No candidate uses `N13ClassEqIff.n13_class_eq_iff` or assumes `exactSpreadLine` coherence.

# Integration and checks

Candidates are delivered only under `comms/candidates/`. For the lead's eventual tests, their intended module locations are the identically named `FLT/Assumptions/MazurProof/` files. In particular install the new chart-comparison module before checking the chooser specification import. Do not treat the input-only source subset as a complete build checkout.

- Input file manifest, 16 files / 161433 bytes: PASS (byte counts, SHA256, Git blob identities)
- Additional pinned configuration retrieval: PASS (three files, recorded separately)
- Source mathematical-meaning cross-review: PASS; not compiler validation
- Static candidate scan for prohibited proof escapes / false-lemma references: PASS
- Existing production source edits: NONE; all six candidates are new
- Lean parse/elaboration/build and every candidate Lean check: NOT RUN
- `#print axioms`: NOT RUN
- B00 global coherent chooser existence: OPEN / NOT PROVED
- B03 specialization additivity and degree-four code bridge: OPEN / NOT PROVED

No `lake`, `lean`, dependency-cache, clone, or project build command was run for this delivery. Source review, file metadata validation, UTF-8 decoding, cryptographic checks, and GitHub publication are the only checks claimed here.

# Transfer manifest and reproducible metadata checks

The [input validation manifest](research-dot-FLT-C13-B03-PLAN-r1-input-validation.json) records each pinned input path, encoding, bytes, SHA256, Git blob identity and URL, plus dispatch identity. Input dispatch SHA is 4870aa5a727ab0de9c843106a0fa562210898714; request bytes 6300 and SHA256 a96f1068762e9b0280d9f971d2128ffb80b6670d60f7d1b4e10f955b5543e153.

The [complete output manifest](research-dot-FLT-C13-B03-PLAN-r1-output-manifest.json) records this response, all six candidates, notes, lane manifests, input validation, and the appended activity log by exact bytes and SHA256. It excludes only itself to avoid a circular hash. The following commands reproduce metadata checks on materialized UTF-8 source/output bytes; these are metadata checks, not Lean checks:

```python
from pathlib import Path
import hashlib, json
m = json.loads(Path("comms/inbox/research-dot-FLT-C13-B03-PLAN-r1-output-manifest.json").read_text())
for f in m["outputs"]:
    b = Path(f["path"]).read_bytes()
    b.decode("utf-8")
    assert len(b) == f["bytes"]
    assert hashlib.sha256(b).hexdigest() == f["sha256"]
    # Git blob identity when required: hashlib.sha1(b"blob " + str(len(b)).encode() + b"\0" + b).hexdigest()
```

Publication uses a single tree/commit based on the fresh own-branch head and a non-force fast-forward. Remote file bytes and final branch head are checked after publication; the publishing receipt carries that verification. No main/source branch, PR, production Lean file, or external agent is modified by this delivery.
