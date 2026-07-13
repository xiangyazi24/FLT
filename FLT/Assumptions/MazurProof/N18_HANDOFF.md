# N18 (order-18 exclusion) — HANDOFF for a fresh model/session

Written 2026-07-12 at model handoff. The previous session (Opus 4.8) oscillated between
over-optimism and over-pessimism; the FACTS below were pinned by independent Python + code
verification and a 3-round design debate (Fable + Opus critic + Fable deep-dive, all converged).
**Trust the verified facts, not any single agent's cost estimate.** Two agents independently
underestimated the work ("one lemma", "2 pages") and both were wrong.

Repo: `/Users/huangx/repos/flt`, branch `n18-remove-native-decide`.
Commits this session: `0977b7bb` (wire endpoint), `8d49202b`/`e4e101bb`/`e2cd4272` (analysis notes).
Durable companions (READ THESE): `N18_FIVE_DESCENT_ANALYSIS.md`, `N18_ADD_CONGR_DESIGN.md`, this file.

--------------------------------------------------------------------------------
## 0. ONE-PARAGRAPH TRUTH

The order-18 endpoint `no_rational_point_of_order_18` reduces to a single live `sorry`:
`CyclicExclusion18.no_five_descent_solution` (an integer system). That reduction is DONE, builds,
axiom-clean except this sorry. **But that "one integer lemma" is NOT elementary — it is the entire
global genus-2 theorem `X₁(18)(ℚ) = {6 cusps}` in disguise.** Closing it needs the MW-FG-free rank-0
machinery (the E₀ route). The E₀ route as currently built is VACUOUS (built on the wrong curve
model). The real remaining work = a multi-week good-model rebuild + a (now-cheap) reduction-mod-5
endpoint. This is comparable in size to the original Route-C build. It is the right path; all
cheaper alternatives are proven dead.

--------------------------------------------------------------------------------
## 1. SETTLED FACTS (independently verified — do NOT re-litigate)

1. **Congruence/`decide` on `no_five_descent_solution` is DEAD.** Universal local witness
   `(A,D,e,f)=(5m,1,1,5m)`, `C=50m²+1` satisfies every positivity/gcd/5-divisibility condition
   exactly over ℤ and both polynomial equations mod EVERY m (verified for many m). lcm kills any CRT
   combination. **No counter-modulus exists.** TRAP: in `ZMod m` with `gcd(m,5)=1`, `(5:ZMod m) ∣ x`
   is vacuously TRUE (5 is a unit) — so any `native_decide`/`decide` of the "5∣e xor 5∣f" condition
   at m=8,9,72,… is a SEMANTIC BUG, not a proof. (Verify script pattern in
   `$CLAUDE_JOB_DIR/tmp/witness_check.py`.)

2. **J₁(18) is ℚ-simple GL₂-type — NO elliptic quotient over ℚ.** Point-counting the genus-2 model
   `y²=x⁶+2x⁵+5x⁴+10x³+10x²+4x+1` gives `#J(𝔽_p)=21,63,84,189,441,441,399` for p=5,7,11,13,17,19,23;
   `gcd=21 ⟹ J(ℚ)_tors=ℤ/21, rank 0`. L-poly is ℚ-IRREDUCIBLE at p=5,7,11,23 (only factors at
   13,17,19 = RM/GL₂-type signature). So the N16-style "sextic factors → elliptic shortcut" is
   structurally UNAVAILABLE. (Script `jac_lpoly.py`.)

3. **The `front_end` map EXISTS: `J₁(18)_L ~ E₀ × E₀` over `L=ℚ(ζ₉)⁺=ℚ(a), a³=3a+1`.** From the
   design corpus `scratch/N18_routeC/Q4366_splitting.md` (explicit Möbius involution + two degree-2
   quotient maps + `a³=3a+1` ring identities + a rational 3-isogeny). VERIFIED numerically:
   `#J(𝔽₁₇)=#J(𝔽₁₉)=441=21²=#E₀(𝔽_p)²` at the primes p≡±1 mod 9 that split completely in L, and the
   L-poly there is the perfect square of E₀'s. `E₀ = 162.c3` (Cremona 162b1), `E₀(ℚ)=ℤ/3` gen by
   `(1,0)`, `E₀(L)=ℤ/21`, `rank E₀(L)=0`. (Script `split_check.py`.)

--------------------------------------------------------------------------------
## 2. THE VACUITY BUG (load-bearing; the previous session's key catch)

`N18Block5Instantiation.no_obstruction18` is a CONDITIONAL taking `red : E0Point →+ RedPoint`,
`hker : ker red = kernelSubgroup`, `front_end` as hypotheses. **Those hypotheses are JOINTLY
UNSATISFIABLE, so the conditional discharges nothing.**

Why (every premise checked in code):
- `E₀=(1,−1,1,−5,5)` has ADDITIVE reduction at 3 (conductor `162=2·3⁴`).
- `kernelSubgroup = {P | P=0 ∨ ordPi(xCoord P) < 0}` (N18Block5Instantiation.lean:205).
- `T := .some 1 0`, `addOrderOf T = 3` proven (`N18RouteC_Isogeny.lean`), `xCoord T = 1`,
  `ordPi 1 = 0`. So `T ∉ kernelSubgroup`.
- `Fintype.card RedPoint = 7` proven (`N18RouteC_Reduction.lean:49`).
- `hker ⟹ red T ≠ 0`; `3•T=0 ⟹ addOrderOf(red T)=3`; Lagrange ⟹ `3 ∣ 7`. Contradiction.

**Root cause:** the kernel/valuation infra uses ℤ-model (additive-at-3) coordinates, where the
order-3 point T has a π-UNIT x-coordinate and is NOT in the formal kernel. T only enters the formal
group in **good-model coordinates over L** (good supersingular reduction, `v(z)=1`).
`N18RouteC_GoodModel.lean` + `N18RouteC_VariableChangePoints.lean` already exist (sorry-free) and are
the intended home. This is the same bug class as the earlier documented `v(z)≥1 → v(x)<0` fix.

--------------------------------------------------------------------------------
## 3. PACKAGE II IS OFF-PATH AND DROPPABLE (not the crux)

Live dependency chain (traced + agreed by all reviewers):
`no_obstruction18` (539) = `front_end ∘ all_points_annihilated_by_21` (524)
  `all_points_annihilated_by_21` ⟸ `Separated.e0_killed_by_21`
      ⟸ `Block4.weak_three_descent` (**PROVEN, sorry-free** — the 3-isogeny descent through T)
      + `Reduction.seven_nsmul` (**PROVEN**)
      + `formalFiltration` ⟸ `val_three_smul_ge` ⟸ `zParam_nsmul_congr` ⟸ **Package I `add_congr`**.
`msq_torsionFree` (Package II) feeds only `torsion_val_eq_one → hC → torsion_annihilated_by_21`,
which is referenced NOWHERE on the live path (dead branch). **Exponent-21 suffices**; `E₀(L)=ℤ/21`
exactly is not needed. Package II, if ever kept, is ~2-3 pages via the division polynomial `Ψ₃`
(`coeff_Ψ₃=3`, Mathlib HAS this) on the good model — NOT the `3f(T)+g(T³)` formal-log route (Mathlib
has NO elliptic formal group / [n]-series: `RingTheory/FormalGroup/Basic.lean` is abstract-only,
`AlgebraicGeometry/EllipticCurve/` has no formal group).

--------------------------------------------------------------------------------
## 4. THE PLAN (3-round nailed ledger) — what Codex must build

**(A) GOOD-MODEL PORT — the real crux (multi-week).** Rebuild `kernelSubgroup`, `val_coords`,
`add_congr`, and the concrete `red`/`hker`/`vpi`/`zParam` on the GOOD model.
- Transport data (from `N18RouteC_GoodModel.lean`): `(u,r,s,t) = (a²−a−3, 3+a−a², 2−a², −8−2a+2a²)`.
  Good model has integral `aᵢ'`, `v(a₄')=v(a₆')=1`, `v(Δ')=0`, reduction = the 7-point curve over 𝔽₃
  (a-invariants `2,2,2,0,0`), `a_π=−3` supersingular.
- On the good model, T=(1,0)→ good coords has `v(z_good)=1` (T enters the formal kernel). The
  Newton-polygon `val_coords` argument survives on `v≥0`, but every "unit" certificate that was a
  π-unit on the ℤ-model becomes an `a³=3a+1` ring computation over L.
- `add_congr` BLUEPRINT is in `N18_ADD_CONGR_DESIGN.md` (ChatGPT Q4613, method verified, incl. a
  caught bug: the naive affine-slope bound `v(ℓ)≥−min` is FALSE — use the chart-normalized line
  `t=−x/y, w=−1/y`, the intercept `b` carries both inputs, and identity (8)). The METHOD transfers;
  **recompute the chart polynomial `G` and coefficients `A,B,C,D` for the GOOD model curve.**

**(B) DISCHARGE `front_end`: `(E₀(L) killed by 21) ⟹ ¬Obstruction18`.** NEW short endpoint from
ChatGPT Q4616 — avoids the 42-fiber elliptic-quotient computation entirely:
- Since `J(ℚ)≅ℤ/21` (prime to 5), reduction at p=5 is INJECTIVE on `C(ℚ)`. `C(𝔽₅)` = exactly the 6
  cusp reductions. The 6 rational cusps already surject onto `C(𝔽₅)`. Therefore `C(ℚ) = {6 cusps}`.
  NON-Chabauty, NO elliptic quotient, NO formal group. Even `[42]J(ℚ)=0` suffices (5∤42... it needs
  21 or 42 killing, prime-to-5).
- Needs: `J(ℚ) killed by 21` (comes from (A) via the splitting `J_L~E₀²` + `E₀(L)` killed by 21),
  `C(𝔽₅)=6 points` (a decidable point count), reduction injectivity on prime-to-5 torsion (standard).
- Suggested Lean lemma names (Q4616): `redJ_kernel_no_primeToFive_torsion`, `cF5_eq_six_cusps`.
- CAVEAT: `rank J(ℚ)=0` alone does NOT give finiteness without MW-FG; the concrete `killed-by-21`
  from (A) is what makes this MW-FG-free. Fable-1's warning: don't let the vacuity fix hide that (B)
  is also currently unproven.

**(C) TRIVIAL BRIDGE (Codex-sized).** `∃ integer solution → ∃ x y:ℚ, 0<x ∧ y²=sextic(x)` via
`(x,y)=(D/A, C/A³)` (needs `C²=F` from the form identity `(e²−2f²)²+8e²f²=(e²+2f²)²` + `ef=AD(A+D)`,
then `field_simp`/`ring`). Then `no_five_descent_solution` follows from the (A)+(B) global result
restated as `no_positive_point`. The endpoint wiring `no_obstruction18 → no_five_descent_solution` is
ALREADY committed (`0977b7bb`) and builds.

Order to execute: (A) first (it gates everything), then (B) [now cheap via Q4616], then (C).

--------------------------------------------------------------------------------
## 5. CHATGPT / ORACLE RESULTS ALREADY IN HAND

- **Q4613 (add_congr blueprint):** full pointwise chart-based design, caught the affine-slope bug →
  saved verbatim-in-substance in `N18_ADD_CONGR_DESIGN.md`. Delivery failed to Notion/GitHub so it
  exists ONLY in that file + the previous session transcript.
- **Q4615 ([3]-series):** rational-model `[3](t)=3t−3t²+9t³−51t⁴+…` (all coeffs ÷3, additive = Ĝₐ);
  good-model has supersingular Newton polygon (1,3)-(3,1)-(9,0), `v(z_T)=1`. Confirms the model issue.
- **Q4616 (front_end / no-Chabauty endpoint):** the reduction-mod-5 short endpoint above. Full text
  was at `/tmp/gpt_Q4616.md` (ephemeral). Key content captured in §4(B).
- **Q4366 (splitting):** `J_L ~ E₀×E₀`, explicit `a³=3a+1` construction. In
  `scratch/N18_routeC/Q4366_splitting.md` (permanent).
- Verify scripts (ephemeral `$CLAUDE_JOB_DIR/tmp/`): `witness_check.py`, `jac_lpoly.py`,
  `split_check.py`, `descent_search.py` — re-runnable to re-confirm §1 facts.

Oracle infra: `python3 ~/.openclaw/workspace/scripts/ask-gpt.py "$(cat q.txt)"` (pass question as
ONE argv arg — passing a bare channel name makes the channel the QUESTION; auto-routes to an idle
`flt`/`shen` tab; `⚡ ALL CONNECTORS FAILED` = delivery timeout, tab still running, DON'T re-send).
See the `/fable-ora` skill for the cost-tiered Fable(premium)/ChatGPT(cheap)/Codex(implements) split.

--------------------------------------------------------------------------------
## 6. WHAT NOT TO REPEAT (previous session's failure mode)

- Do NOT trust a single agent's size estimate. Verify against the code dependency graph + Python.
  ("one lemma away" and "Package II, 2 pages" were both wrong.)
- Do NOT try to close `no_five_descent_solution` by any congruence / finite `decide` — proven dead
  (§1.1), and the ZMod-5-unit trap makes false "successes" look real.
- Do NOT build formal-group machinery on the ℤ-model — it is additive at 3 and yields vacuous
  interfaces (§2). Everything formal-kernel goes on the GOOD model.
- The order-18 result IS classical/elementary math (Kubert-era; "not new, not publishable" per
  `ROADMAP.md` Novelty note). The novelty is the axiom-free MW-FG-free Lean formalization. This exact
  formalization-ready route (Route C + the elementary five-descent) is OUR construction (design corpus
  `scratch/N18_routeC/Q43xx–Q45xx`), not transcribed from a single paper.
