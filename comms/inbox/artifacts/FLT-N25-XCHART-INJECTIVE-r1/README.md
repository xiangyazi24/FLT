# Actual N25 X-chart fraction-map injectivity

## Result

Production candidate `N25F_XChartFractionInjective.lean` proves
`MazurProof.N25F_XChartFractionInjective.xChartToFraction_injective`:

```lean
Function.Injective N25F_XChartFractionMap.xChartToFraction
```

It imports the independently delivered map and chart-equivalence candidates.
The production statement adds no premise, carrier, geometric hypothesis,
axiom, sorry, or admission. This is the actual coordinate-rigid map on the
source's `XChartRing`, not the automorphism-induced X/W equivalence.

The proof contains:

1. A generic finite-image lemma: a noninjective map from a one-dimensional
   finite-type binary algebra into a field sends every nonzero image element
   to an element of finite positive multiplicative order. The kernel is a
   nonzero prime, hence maximal; Zariski's lemma makes its residue field finite.
2. `originEval`, a genuine lift through the actual W-chart quotient, evaluating
   at the canonical binary curve point `[0:0:0:1]`.
3. `originEval_qx = 0` and `qx_pow_ne_one`: no positive power of `qx` is one.
4. The dimension bound on X, transported through the actual algebra
   equivalence from the accepted W Dedekind instance. If the fraction map
   were noninjective, the proven formula `xW ↦ 1/qx` and the finite-image lemma
   would force a positive power of `qx` to be one, a contradiction.

The required finite-type structure on X is inferred from its actual finite
multivariable-polynomial quotient presentation, not passed as a harness
premise. The actual origin evaluation and power obstruction need no domain
or dimension assumption.

## Bounded verification

The complete actual-source harness `XChartInjectiveCheck.lean` passed on
Lean 4.31.0-rc2 and Mathlib `96fd0fff3b8837985ae21dd02e712cb5df72ec05`:

- `actual-01`: exit 0, 28.168 seconds, 2,503,388 KiB peak child RSS
- Single compiler thread, 60-second timeout, 3072 MiB cap
- `originEval`, `originEval_qx`, `qx_pow_ne_one`, and the injectivity theorem
  report only `propext`, `Classical.choice`, and `Quot.sound`
- No `sorryAx` or custom axiom occurs in the successful result
- Non-fatal style warnings are retained in the raw log

The smaller generic lemma also passed separately in `generic-02`; the
initial generic-01 elaboration failure is retained. It required explicitly
unfolding the local kernel abbreviation in two simplifications.

The harness reproduces 51 verbatim declarations from 11 accepted source
files, including the actual chart carrier and relations, and checks both
prerequisite candidate bodies and the entire new production body. All 14
provided source snapshots match the Git blob SHA-1 and SHA-256 manifests at
accepted FLT commit `f0eb8381677bc483bddd93826871845030dd5c0e`.

The harness explicitly supplies `[IsDomain W]` where needed in the prior
candidate bodies and `[IsDedekindDomain W]` immediately before the final new
injectivity proof. These ordinary structural parameters stand for accepted
source instances, especially `canonicalWChart_isDedekindDomain` in
`RationalPointsN25QuotientTwoWChartNormalization.lean`, lines 573–574. They
are not new production premises. The production import graph supplies them.
The X-chart dimension instance itself is proved by transport, and its
finite-type instance is synthesized from the actual source presentation.

This is not a full FLT import-graph build. `ActualXChartInjectiveCheck.lean`
is the pending full-import acceptance check to run after the three candidates
are integrated into the pinned FLT checkout. It has not been run here.

## Reproduction and integrity

`make_check.py` reconstructs the tested harness from local exact sources and
unchanged prerequisite snapshots. Regeneration was verified byte-for-byte
against the successfully checked file. `make_candidate.py` likewise
reconstructs the new candidate. `source-inputs.json` and
`copied-declarations.json` identify source blobs and extracted ranges;
`validation.json` records compiler evidence and all candidate hashes.

Use the existing bounded wrapper, without a broad build:

```sh
python /workspace/shared/flt-n25-xchart-injective/make_check.py
python /workspace/shared/flt-n25-xchart-injective/run_check.py check-local \
  /workspace/shared/flt-n25-xchart-injective/XChartInjectiveCheck.lean
```

No accepted source was modified. No remote write, commit, full build, or
cache-mass operation was performed.

## Repository packet layout

Source snapshots can be fetched at the exact URLs and hashes recorded in
`source-inputs.json`; they are not duplicated in this packet. The two
`prerequisites/` source files are the unchanged candidates already delivered
at commits `44f3f126715e57961d25dd4f3a9a451d3a0a911f` and
`2dcb8643f3cac5a726a7425d1890770c94c38a26`. Place the exact files under those
local subdirectories to reproduce the harness. `validation.json` verifies
their hashes as part of the tested assembly.
