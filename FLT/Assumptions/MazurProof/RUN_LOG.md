
## Run 2026-06-20 (keystone campaign, autonomous drive)
- Design: 6 ChatGPT rounds (dm1/2/3) consolidated to scratch/Keystone_MasterDesign.md.
  Campaign reduced to FOUR named seams (axiom-as-seam): prePsi'_separable (core1 etaleness),
  xRep coord formula (core1, provable EDS induction), Weil pairing geom props (core2),
  rational_torsion_finite (already derivable from existing mordell_weil_fg axiom).
- DECISIONS (autonomous, per Xiang "don't ask me to decide"):
  * Finiteness leg: NO new axiom. Derive rational_torsion_finite from the EXISTING
    mordell_weil_fg axiom (rational_torsion_finite_alias already does this via
    torsion_set_finite_of_fg). Discharge rational_torsion_two_invariant_factors -> axiom 6 to 5
    using only existing axioms. Full Mordell-Weil = separate later campaign.
  * Stage-0: adopt dm3 API refactor (geomNTorsion/mapLinear, AddEquiv -> LinearEquiv).
- Two self-corrections caught by verification: (1) nondegeneracy of Weil pairing does NOT
  follow from cardinality (keep as geometric package field); (2) Weil reciprocity needs
  tame-symbol calculus + resultants, not naive disjoint induction.
- Builds dispatched (Codex Pro xhigh, isolated flt-ai repo):
  * scratch/InvariantFactors.lean -- pure-algebra invariant-factor lemma (B tail), 0-axiom.
  * scratch/NTorsionCard.lean -- KEYSTONE n_torsion_card=n^2 modulo the 2 core-1 seams.
- Baseline: 6 axioms; campaign targets 3 (rational_torsion_two_invariant_factors,
  weil_pairing_primitive_root, and mordell_weil_fg feeds the first).
