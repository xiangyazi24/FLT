# Independent static review

Status: **SOURCE-CONSISTENT; UNCOMPILED / NOT_CONFIRMED**.

Reviewed `N25F_HighDegreeEffective.UNCOMPILED.lean` against the seven supplied
reference files. No required repair was found in this narrow candidate. This is
source inspection, not an elaboration, kernel check, or axiom audit. The
`CoarseLowerBound` candidate and full actual-geometry dependency closure remain
UNCOMPILED / NOT_CONFIRMED. No Lean, Lake, build, cache, Slurm, SSH, or Git
mutation/publication was performed; the candidate was not changed.

Reviewed candidate SHA-256:
`1ded9a6818a558e0df8aeaf4a4342368c312e15f926a4eca5b9d4a0ab1749cdc`.

## Interface and proof checks

- **Positive finrank (candidate lines 30–36):** the supplied
  `N25F_CoarseLowerBound.UNCOMPILED.lean:181–185` states exactly
  `degree D ≤ (finrank (ZMod 2) (fullRiemannRochSpace25Two D) : ℤ) + 4 * B`.
  Combining this with `4 * B < degree D` forces positive natural finrank.
  This is the linear integer/natural arithmetic intended for `omega`; no
  positivity assumption on the individual coefficients of `D` is added.
- **Nonzero actual section (lines 40–49):**
  `Finite.lean:378–386` confirms the qualified theorem name
  `Module.finrank_pos_iff_exists_ne_zero`, named arguments `R` and `M`, and
  the `.mp` conclusion `∃ x : M, x ≠ 0`. Its finite-module requirement is
  supplied by the declared instance in `N25F_SectionFiniteness.lean:88–89`.
  The remaining ring/domain/torsion-free/strong-rank-condition requirements
  are the standard ones for a vector space over `ZMod 2`; their actual
  synthesis has not been tested. `NonzeroSection25Two D` is exactly
  `{f : fullRiemannRochSpace25Two D // f ≠ 0}` (lines 19–20), so the nested
  constructor is the right one.
- **Nonzero submodule (lines 53–61):** `Finite.lean:372–373` confirms that
  `finrank_bot` is a root-level theorem with the expected submodule type.
  Rewriting the positive finrank hypothesis to `0 < 0` gives precisely the
  contradiction used by `Nat.lt_irrefl 0`.
- **Effective representative (lines 66–77):**
  `N25F_SectionClassFiber.lean:20–29` defines the target fiber with exactly
  the same `EffDivOfDegree`, `effectiveToDivisor`, subgroup, equality
  orientation, and divisor argument as the candidate. Projecting the
  existing map's value and property directly proves the requested existential.

## Scope and exact degree

Every theorem quantifies over arbitrary `ProjectiveDivisor25Two D`, with only
the strict threshold hypothesis. There is no effective-divisor premise,
generic Riemann–Roch premise, restriction to small-degree support, substituted
formal section space, or new numerical claim about the bound.

The section space is the actual curve-field submodule with the bounded-pole
inequality at **every** carrier point (`N25F_RiemannRochSpace.lean:31–35`). The
principal subgroup is the range of the actual principal-divisor map, and class
equality is characterized by an actual nonzero curve function
(`N25F_FullPicardDegree.lean:17–18,42–49`).

The `.toNat` in `EffDivOfDegree (degree D).toNat` does not weaken the degree
claim here: `B : ℕ` (`N25F_WBasisPoleBound.lean:33–37`), so the strict threshold
implies `0 < degree D`, and therefore `((degree D).toNat : ℤ) = degree D`.
Independently, the imported section-to-effective construction proves the
integer degree equality using the actual product formula
(`N25F_SectionFiniteness.lean:47–55`). An additional corollary displaying
integer degree equality explicitly could help readers, but is not a required
fix and is not needed to make this statement exact.

## Trust boundary

No `axiom`, `sorry`, `admit`, `unsafe`, or replacement definition occurs in
the reviewed candidate. This does **not** establish absence of `sorryAx` or
other unexpected dependencies in the transitive closure. The supplied
prospective audit commands are appropriate future checks; they were not run.
The references establish the immediate API shapes, not successful imports,
instance synthesis, tactic execution, or correctness of the complete closure.
