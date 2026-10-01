TASK_ID: FLT-C13-B03-PLAN
REVISION: 1
TYPE: TASK
STATUS: OPEN
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: a6290bc36c3549d89239da82b13b1f59ebd0388e
SCOPE: C13 axiom (CyclicExclusion13.C13Sextic_affine_x_is_cuspidal). Source audit + proof design + uncompiled candidate Lean for
  (B03) additivity of specialization into the explicit ZMod 19 special code, and (B00) the coherent global chooser it needs.
ACCEPTANCE: see "Deliverable" below. Uncompiled candidates are expected (no toolchain on your side); mark every Lean check NOT RUN.
  The lead/local executor will compile; acceptance of code is the lead's lake build + #print axioms, not yours.
SUPERSEDES: none
NONCE: FLT-DOT-20261001

## Background (all at SOURCE_COMMIT, axiom-clean unless noted)
- G := N13RationalPointEndgame.G (rational Picard group of the C13 sextic model); AJ13 (N13Jacobian.lean).
- Special target: N13AbelFiberTwoModel.PicTwoSetModel (19-element set quotient). N13SpecialAbelCode(.Quotient).lean give
  picEquiv : PicTwoSetModel ≃ ZMod 19 and specialTranslateCode r (translation, code(translate r c) = code c + r).
- Degree-zero coherent realizations: N13InfinityPointPicardRealization.infinityPlusData, .infinityMinusData,
  N13InverseInfinityWitness.inverseInfinityData (special divisor C+A, generic class (1,0,2), saturated).
- NOT coherent: N13RationalPicardSpreadExistence.exactSpreadLine (degree-zero branch reorients infinityPlusData, keeping its
  special divisor); counterexample N13CoherentPointReduction.exactRaw_saturated_does_not_determine_specialClass.
- Pointwise coherent: N13RationalCurvePointPicardRealization.pointSpreadLine / data P .special_eq.

## Questions
1. B00: design a global chooser c : G → N13TwoChartPicardRealization.Data (or a family) whose witness carries a
   specialization-compatibility field, built from the three degree-zero data above + existing degree-1/2 constructions
   (cite exact declarations). State the Lean structure/definition and the existence theorem precisely.
2. B03: the theorem specialCode (P + Q) = specialCode P + specialCode Q in ZMod 19 for the chooser's special class composed with
   picEquiv (re-centred so specialCode 0 = 0). Give the mathematical proof in terms of the repo's two-chart data (tensor of lines,
   N13TwoChartLineTensor; reduction maps) and an honest list of any infrastructure the repo lacks.
3. A dependency-ordered list of small lemmas (exact Lean statements, target new file names, which existing declarations each uses).
4. Uncompiled candidate Lean for as many of the first lemmas as you can, as files under comms/candidates/ on your output branch
   (new-file style, namespace MazurProof.N13...). Mark them NOT RUN.

## Deliverable
comms/inbox/research-dot-FLT-C13-B03-PLAN-r1.md (+ comms/candidates/*.lean), with: source pin, manifest of your outputs
(path, encoding, bytes, sha256), PASS/FAIL/NOT RUN per check, and citations by exact declaration name + file at SOURCE_COMMIT.
Rules: no sorry/admit/axiom/native_decide/True placeholders in candidates; no edits to existing files or statements; do not
build on N13ClassEqIff.n13_class_eq_iff or on exactSpreadLine coherence.

## Input manifest (files at SOURCE_COMMIT)
```json
{"source_commit": "a6290bc36c3549d89239da82b13b1f59ebd0388e", "files": [
  {"path": "FLT/Assumptions/MazurProof/N13SpecialAbelCode.lean", "encoding": "utf-8", "bytes": 2189, "sha256": "ef95b5992c1798bdd78b481ab824f23f60786fe40eb2cecd59ebe146c870a38b"},
  {"path": "FLT/Assumptions/MazurProof/N13SpecialAbelCodeQuotient.lean", "encoding": "utf-8", "bytes": 4984, "sha256": "89aa5cc8938f8210044d169a43e5eaf363a8aa9f9bcbd2e6847e1fed9a2bd317"},
  {"path": "FLT/Assumptions/MazurProof/N13AbelFiberTwoModel.lean", "encoding": "utf-8", "bytes": 9325, "sha256": "6e6c06e4eff7957214a3600ba6e21b8da78ced6fec95d3f53210edcaacdf4f95"},
  {"path": "FLT/Assumptions/MazurProof/N13SymmetricSquareTwo.lean", "encoding": "utf-8", "bytes": 4991, "sha256": "d078c1db6498782841c59f411007cbf8b9198d94afb995e292be4a4ca4f14114"},
  {"path": "FLT/Assumptions/MazurProof/N13SpecializationGroupHom.lean", "encoding": "utf-8", "bytes": 2681, "sha256": "ba455effe1c2fcc6201d72559341b454f2ca2e99d943ab4d4e8fa06fa7d5bced"},
  {"path": "FLT/Assumptions/MazurProof/N13TwoChartPicardRealization.lean", "encoding": "utf-8", "bytes": 11991, "sha256": "1c3631df108c3d64669026f0630bc25b6d8e7be52d0857ceb5ab1b1474601b9e"},
  {"path": "FLT/Assumptions/MazurProof/N13TwoChartLineTensor.lean", "encoding": "utf-8", "bytes": 22140, "sha256": "e969baf707a84719a623b04e356461806592a19ff7bdf29958e3071e99bf0f59"},
  {"path": "FLT/Assumptions/MazurProof/N13RationalPicardSpreadExistence.lean", "encoding": "utf-8", "bytes": 26777, "sha256": "99db457cab7aa318f887684378f74ad73d8d3f9f61260deb301539c374747cbd"},
  {"path": "FLT/Assumptions/MazurProof/N13InfinityPointPicardRealization.lean", "encoding": "utf-8", "bytes": 9643, "sha256": "283cbf46150d69b9c6e958dfbb9e42acb3908c845125e5c4bcd0b3ffdee017ce"},
  {"path": "FLT/Assumptions/MazurProof/N13InverseInfinityWitness.lean", "encoding": "utf-8", "bytes": 4776, "sha256": "e72f6a9a45dcae66f4d47c35fdb26f76fe3fa21285125d781a2586763d945b62"},
  {"path": "FLT/Assumptions/MazurProof/N13InverseInfinityWitnessClass.lean", "encoding": "utf-8", "bytes": 6421, "sha256": "3a6f466b30639f60a8d43f8265319ecf8ab2aed131ad2c1d74a38aeb0196f88e"},
  {"path": "FLT/Assumptions/MazurProof/N13OppositeInfinityClass.lean", "encoding": "utf-8", "bytes": 4693, "sha256": "65986dd42af431632b3bf7764c4f0f21c9ff80e7af96001d93d1088c628e50a8"},
  {"path": "FLT/Assumptions/MazurProof/N13CoherentPointReduction.lean", "encoding": "utf-8", "bytes": 5594, "sha256": "a5453dfdddabef0f2fba26161ce8073ccf57157ac503d84030f9d29a4eedd79f"},
  {"path": "FLT/Assumptions/MazurProof/N13RationalPointEndgame.lean", "encoding": "utf-8", "bytes": 5900, "sha256": "8cf54292128293da74cb5411c5d667cfcbcccba743dfd6caa0e28262010f7cf0"},
  {"path": "FLT/Assumptions/MazurProof/N13RationalCurvePointPicardRealization.lean", "encoding": "utf-8", "bytes": 28758, "sha256": "4da73ff1ac7268fc02f20740c129bb529dc65ccb3c68a27655e6cbfe9b61218f"},
  {"path": "FLT/Assumptions/MazurProof/N13Jacobian.lean", "encoding": "utf-8", "bytes": 10570, "sha256": "5ebe0a39be24822c485ee4671316cb6d67f41b536758c4783280901280bbd833"}
]}
```
