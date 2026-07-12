# N18 REDIRECT — close no_obstruction18 via the VERIFIED Block-5 scaffold

The previous Codex ground ~9h with 0 commits on the WRONG Block-5 object (supersingular
height-2 `[3]`-series Newton polygon). It has been stopped. Its infrastructure (the ~46
`N18RouteC_*.lean` files: E₀ split over L=ℚ(ζ₉)⁺, Block-4 weak 3-descent, push-pull, cyclotomic
units, etc.) is UNCOMMITTED but PRESENT in your working tree — REUSE it, do not rebuild.

## The single goal
Close `no_obstruction18 : ¬ ∃ b c X : ℚ, Obstruction18 b c X` (CyclicExclusion18.lean:58) — the
last N18 sorry. It reduces to: **E₀=162.c3 has rank 0 over L, and E₀(L)_tors is annihilated by
[21]** ⇒ E₀(L)=ℤ/21 finite ⇒ Jacobian finite ⇒ C(ℚ)=cusps ⇒ no order-18 point.

## ⚠️ Block-5 is ALREADY PROVED — instantiate it, do NOT re-derive it
`FLT/Assumptions/MazurProof/N18Block5FormalKernel.lean` is a VERIFIED (0 sorry, axiom-clean,
builds) Fable-designed proof of the Block-5 core over an abstract interface `FormalKernel18`
(Ê₀(𝔪) of E₀ at π|3). It PROVES, height-agnostically (NO Newton polygon):
- `no_prime_to_3_torsion` (Lemma A), `three_power_torsion_exponent_three` (Lemma C),
  `annihilated_by_21` (the [21] assembly by per-element Bézout).
Also read `CODEX_SPEC_N18_BLOCK5_RETARGET.md` for the math. RETIRE the old
`N18RouteC_Separated / LocalThree*` Newton-polygon route.

**Your Block-5 job = INSTANTIATE `FormalKernel18` for the real E₀ formal group:**
1. Build a term `FK : FormalKernel18` with `M` = the actual Ê₀(𝔪_L) (kernel of reduction), by
   proving its fields from the concrete `[m]`/`[3]` multiplication series over 𝒪_L:
   - `val_eq_top`, `one_le_val`: from the parameter valuation z=−x/y on the formal kernel.
   - `val_unit_smul` (A): `[m]T = m·T + O(T²)` with m a unit (3∤m) ⇒ valuation preserved.
   - `val_three_smul_ge` (C): `[3]T = 3T + T²·A(T)`, v(3)=3 ⇒ `v([3]z) ≥ min{3+v(z), 2v(z)}`
     (LOWER bound only — do NOT use any z³/z⁹ leading term).
   - `torsion_val_eq_one` (B): the ONE deep input (formal-log iso Ê(𝔪²)≅(𝔪²,+), n=2 since
     e=3,p=3, Silverman AEC IV.6.4(b)). If Mathlib lacks the formal-log iso, **package B as ONE
     named hypothesis** and proceed — do NOT grind p-adic log convergence.
2. Supply the two assembly inputs to `annihilated_by_21`:
   - `hC`: from Lemma C + supersingular connectedness (E₀[3^∞] reduces INTO Ê₀(𝔪), so 3-power
     torsion of E₀(L) lands in M). Note: the order-3 point T IS a nonzero formal 3-torsion pt —
     that is EXPECTED, do not try to exclude it.
   - `hQ`: from Lemma A at a SECOND good prime 𝔮 + the decidable `#Ẽ₀(𝔽_𝔮)=7` (prime-to-3
     residue bound). Keep this a separate cheap decidable goal.
3. Conclude E₀(L)_tors killed by [21], combine with Block-4 (E₀(L)=⟨T⟩+3E₀(L), rank 0) ⇒
   E₀(L)=ℤ/21, and wire through the existing N18 pipeline to `no_obstruction18`.

## Sanity-check (Fable-flagged) before trusting B's e-value
Confirm E₀ has GOOD supersingular reduction at π over L (not merely potentially-good/additive),
and e=v(3)=3, v(π)=1. If reduction at π is only potentially good, B's threshold shifts.

## Build (NFS uisai2 — NEVER /dev/shm)
Your NFS build dir is `~/repos/flt-n18` (mathlib symlinked to the shared bucket; do NOT lake
update). Edit locally, then each cycle:
```bash
rsync -a --delete --exclude='/.git/' --exclude='/.lake/' \
    <your local repo>/ uisai2:/home/xhuan5/repos/flt-n18/
ssh uisai2 'export PATH=$HOME/.elan/bin:$PATH; cd ~/repos/flt-n18 && \
    nice -n 15 lake build FLT.Assumptions.MazurProof.CyclicExclusion18 2>&1 | tail -40'
```
Some of the ~46 inherited files may be mid-write (previous Codex was stopped mid-edit) — fix
build errors as you go. `N18Block5FormalKernel.lean` already builds clean.

## Acceptance
1. `rg -c '\bsorry\b|sorryAx' N18*.lean CyclicExclusion18.lean` = 0 (EXCEPT: if the formal-log iso
   for B is a genuine Mathlib hole, isolate B as exactly ONE named hypothesis and close everything
   else — report it precisely).
2. `#print axioms MazurProof.CyclicExclusion18.no_rational_point_of_order_18` =
   `[propext, Classical.choice, Quot.sound]` (or clean-modulo-the-one-B-hypothesis).
3. Commit with `git add <specific N18 files>` (NOT -A) on your branch.
NO effort ceiling. Do NOT resurrect the Newton-polygon route. Instantiate the verified scaffold.
