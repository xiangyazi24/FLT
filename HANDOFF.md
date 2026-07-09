# Session Handoff — 2026-07-08 (FLT Mazur sorry elimination)

automode: yes

## Achievements

### CyclicExclusion20: ALL 7 sorry CLOSED (commit 20ff9cfa)
- 5 group-theory lemmas: image_order_10/12, eta_ne_half_20/24, helpers
- 2 final wiring: Z/2×Z/10 and Z/2×Z/12 injective embedding
  via coprod + ZMod.lift + eq_five/six_nsmul independence
- 1 axiom remains: exists_rational_two_isogeny_quotient

### RationalPointsN14 + DescentBridgeN14 wired (commit cef30929)
- import scratch.ObstructionN14 → axiom → theorem
- NEEDS REMOTE BUILD on uisai2 (local mini has no scratch oleans)
- Would close 1 sorry + 1 axiom

### CyclicExclusion15: false statement FIXED (commit 3b0e38e6)
- no_tate_order5_psi3_root_solution was FALSE (b=-2, x=-1 counterexample)
- Added TateOrder5CurveEq constraint

### F11_param_identity PROVED (commit 80745463)
- F₁₁(c+c²t, c) = -c⁸·Q(c,t) compiles clean
- Reduces F₁₁=0 to elliptic curve Y²=X³+8X²+16X+16 = 11a3

### Total: 7 sorry closed, 1 axiom discharged (pending remote), 1 fix

## 11a3 Rank-0 Certificate (COMPLETE, ready for Codex)

The 2-descent certificate for 11a3 (y²+y=x³-x²) is fully worked out:

**Setup:**
- K = Q(β), β³-2β²+2=0, disc=-44
- f(X) = X³-2X²+2, curve is f(X) = 2z²
- Bad primes: S = {2, 11}

**Candidate group (norm-2 coset):**
{-β, -β·η, -β·π, -β·η·π} where η=1-β, π=β²+β+3

**Local obstructions (all verified):**
1. η class: f(1)=1, need 1=2z² over Q₂ — IMPOSSIBLE (v₂ parity)
2. π class: covering eq gives 11·s₂=1 — IMPOSSIBLE mod 11
3. η·π class: covering eq gives 11(s₁+s₂)=-1 — IMPOSSIBLE mod 11

→ Sel²(E/Q) = 0 → rank = 0

**Formalization route:**
All checks are finite: irreducibility (rational root), norm computations (norm_num),
mod-11 contradictions (norm_num), v₂ parity (valuation). Suitable for Codex.

**ChatGPT answers on xiang/scratch:** Q4012 (certificate), Q4013 (eta correction)

## Remaining: 12 sorry in MazurProof/

### Category A: Tate NF Bridge (4 sorry)
All need general Tate NF reduction (not in Mathlib):
- CyclicExclusion11:173, CyclicExclusion15:155
- CyclicExclusion18:29, CyclicExclusion21:34

### Category B: Diophantine (4 sorry)
- CyclicExclusion11:185 — F₁₁ reduces to 11a3, rank-0 certificate READY
- CyclicExclusion15:172 — X₁(15), rank 0, similar approach needed
- CyclicExclusion18:32 — X₁(18), genus 2, needs Chabauty
- CyclicExclusion21:37 — similar

### Category C: Kubert Bridge (4 sorry)
- CyclicExclusion14:77 — needs Vélu isogeny computation (NOT discriminant route)
- CyclicExclusion16:112 — similar
- KubertBridgeN16:288, :307 — explicit birational map

## Key Mathematical Findings

1. Y²=X³+8X²+16X+16 IS 11a3 (same c4=16, c6=-152, Δ=-11, j=-4096/11)
2. Kubert bridge N14: standard curve w²+uw+w=u³-u ≠ 96A1 (different j)
   Correct route: keep rational root X of T₂, do Vélu isogeny
3. X₁(18) is genus 2 (ChatGPT Q3921 confirmed)
4. F₁₁ mod-2 only proves v₂(b)≠0, not full impossibility (Q3950)
5. 2-descent uses f(X)=2z² (not z²!) — norm target is 2, not 1 (Q4013)

## Files Modified (on ai-scratch branch)

- FLT/Assumptions/MazurProof/CyclicExclusion20.lean — 0 sorry ✓
- FLT/Assumptions/MazurProof/CyclicExclusion15.lean — bug fixed
- FLT/Assumptions/MazurProof/RationalPointsN14.lean — wired (needs remote build)
- FLT/Assumptions/MazurProof/DescentBridgeN14.lean — axiom→theorem (needs remote build)
- scratch/TestZ2Z10.lean, TestExcl20Final.lean, TestF11.lean — infrastructure

## Next Actions

1. **Remote build on uisai2** — verify RationalPointsN14 + DescentBridgeN14 wiring
2. **Codex: 11a3 rank-0 formalization** — certificate is complete, all finite checks
3. **Codex: Vélu isogeny for N14 Kubert bridge** — polynomial computation
4. **Push ai-scratch to xiang remote** for uisai2 build

## Build

uisai2 at /home/xhuan5/repos/flt-ai. Push to `xiang` remote.
Local `lake build` forbidden (24GB mini). Use `lake env lean` for single-file checks.
