# N18 — `no_five_descent_solution` analysis (the sole remaining N18 lemma)

After the Route-1 pivot (commit 0977b7bb), the ENTIRE order-18 exclusion reduces to
one elementary integer lemma in `CyclicExclusion18.lean`:

```
no_five_descent_solution : ¬ ∃ A D C e f : ℤ,
  0<A ∧ 0<D ∧ 0<e ∧ 0<f ∧
  gcd A D = 1 ∧ gcd A (A+D) = 1 ∧ gcd D (A+D) = 1 ∧ gcd e f = 1 ∧
  e*f = A*D*(A+D) ∧
  ((normReal A D = e²-2f² ∧ |C| = e²+2f²) ∨ (normReal A D = 2e²-f² ∧ |C| = 2e²+f²)) ∧
  (5|e xor 5|f) ∧
  (5 | exactly one of {A, D, A+D})
```
with `normReal A D = -A³ - A²D + 2AD² + D³`.

`no_rational_point_of_order_18` axiom trace = `[propext, sorryAx, Classical.choice, Quot.sound]`
— the ONLY hole is this `sorryAx`; no `ofReduceBool` (the dead-code `N18RouteC_LocalThree*`
`native_decide` is NOT on this path).

## Verified facts (empirical + structural)

Let `N := normReal A D`, `M := 2AD(A+D)`, and
`F := A⁶+2A⁵D+5A⁴D²+10A³D³+10A²D⁴+4AD⁵+D⁶`.

1. **`F = N² + 2M²`** (proven in `RationalPointsN18Descent.F18Positive_norm`).
2. **Both descent forms force `F` to be a perfect square**: form (a) `N=e²-2f²`, `M=2ef`
   gives `F=(e²+2f²)²=|C|²`; form (b) gives `F=(2e²+f²)²=|C|²`. So `|C|=√F`.
3. **Empirical (highest authority, `scripts` in job tmp):** for pairwise-coprime `A,D` in
   `[1,600)`, `F` is a perfect square in **0** cases (even ignoring the 5-conditions). Full
   system search `A,D<400`: **0 solutions.** ⇒ the lemma is TRUE (statement not mis-transcribed).
4. **`Z[√-2]` equivalence (class number 1, PID):** `F=k²` with `gcd(N,M)=1` ⟺
   `N+M√-2 = unit·(a+b√-2)²` ⟺ `∃ a,b: ab = AD(A+D) ∧ a²-2b² = N` — i.e. EXACTLY form (a)
   (form (b) is the `√-2·square` branch). So "F never a perfect square for coprime A,D" and
   the five-descent unsatisfiability are the SAME statement; the descent IS the content.
5. **mod-5 alone is INSUFFICIENT:** in every {form a/b}×{5|e or 5|f} combination the achievable
   `N mod 5` covers all of `{1,2,3,4}`, and `N ≢ 0 (mod 5)` always holds — no contradiction at
   mod 5. The obstruction needs mod 25 / the 5-adic valuation of `F`, or the `Z[√-2]` descent.

## Proof strategy (dispatched to ChatGPT flt1/2/3, cross-validated)

- **flt3:** broad — smallest single modulus that kills the system, else the descent step.
- **flt1:** sharp — tabulate `N mod m` vs achievable `e²-2f² / 2e²-f² mod m` for m∈{5,8,9,25,40,72,200}.
- **flt2:** independent `Z[√-2]` / class-group attack via the splitting of 5.

**Verification gate for any answer:** must be consistent with facts 3–5 above. Reject any
"mod 5 closes it" claim. The correct proof either (i) shows `N²+2M²` is never a perfect square
for coprime `A,D` (Z[√-2] descent), or (ii) uses the 5-adic conditions for a cleaner elementary
route. Prefer the route that formalizes with a SMALL decidable congruence + coprimality, not a
large `decide`.

## VERDICT (Fable audit + ChatGPT flt1/Q4610, both independently verified) — 2026-07-12

**`no_five_descent_solution` is NOT elementarily provable. Congruence/`decide` is DEAD, not hard.**

- **Universal local witness** `(A,D,e,f) = (5m, 1, 1, 5m)`, `C = 50m²+1` (Fable verified sympy +
  numeric to m≤2000): for EVERY modulus `m` it satisfies all positivity/gcd/5-conditions exactly
  over ℤ, and `e·f ≡ AD(A+D)` and `normReal ≡ e²−2f²` mod `m`. lcm kills any CRT combination.
  ⇒ **no counter-modulus exists.** Any mod-m "proof" exploits the ZMod-unit bug
  (`(5 : ZMod m) ∣ x` is vacuously true when `gcd(m,5)=1`) or an unsound gcd/positivity encoding.
- **The obstruction is GLOBAL:** `F/A⁶` with `x=D/A` is the genus-2 model of X₁(18)
  (`x⁶+4x⁵+10x⁴+10x³+5x²+2x+1`); an integer solution = a rational point with `x=D/A>0`. The
  contradiction IS the theorem `X₁(18)(ℚ) = {6 cusps}` (finite x-coords 0, −1).
- **No elliptic-quotient shortcut:** Fable's independent L-poly computation gives
  `#J(𝔽_p) = 21,63,84,189,441,441,399` for p=5..23 (gcd 21 ⇒ `J(ℚ)_tors=ℤ/21`, rank 0); the
  L-polys are ℚ-irreducible and split over ℚ(ζ₃) ⇒ **J₁(18) is ℚ-simple GL₂-type — provably no
  elliptic quotient over ℚ.** The N16 miracle (sextic factors → Fermat quartic) is structurally
  absent, not merely undiscovered.

**Pivot verdict: real value, but relocated (not removed) the mountain.** The elementary chain
(`RationalPointsN18Descent`, sorry-free) is a PROVED chunk of what Route-2's `front_end` only
CARRIES as a hypothesis; the pivot cleaned the axiom trace and crystallized the interface. But
the `sorry` contains 100% of the global content — `no_five_descent_solution` is NOT independent
of the E₀ route, it FOLLOWS from it. Route 1 proved the front half of `front_end`; Route 2
supplies the group-theoretic half. **They are two halves of one proof and must be reunited.**

## PATH FORWARD (Fable option (a) — reunite Route 1 + Route 2). Rank 0 ⇒ NO Chabauty.

1. **Easy bridge (Codex-sized):** prove `∃ integer solution → ∃ x y : ℚ, 0<x ∧ y²=sextic(x)`
   via `(x,y)=(D/A, C/A³)` (needs `C²=F` from the form identity `(e²−2f²)²+8e²f²=(e²+2f²)²`
   + `ef=AD(A+D)`, then field_simp/ring). Restate the global target as weak `no_positive_point`
   (only `x>0` needed); make `no_five_descent_solution` its corollary. This is exactly the shape
   Route 2 feeds.
2. **THE single hard core = Package II** `Ê₀(𝔪²)` torsion-free — NOT a Mathlib mountain, a ~2-page
   self-contained formal-group argument on the existing `vpi`/`zParam` infra: from
   `[3](T)=3f(T)+g(T³)` and `v(3)=3`, for `v(z)=k`: `v(3f(z))=3+k` vs `v(g(z³))≥3k`; `k=1`
   allows the order-3 point, `k≥2` gives `v([3]z)=3+k` finite ⇒ `[3]z≠0`. **Dispatched as sharp
   lemma Q4615.**
3. **Geometric middle (front_end's other half):** explicit `L=ℚ(ζ₉)⁺` maps `C→E₀`
   (ring-checkable via `a³=3a+1`, Q4366 design) + finite fiber computation over `E₀(L)` torsion.
   `C(ℚ)⊂C(L)→E₀(L)=` finite explicit set; fibers by field algebra. No Chabauty (rank 0).
4. **Rejected:** genus-2 Chabauty (rank-0 makes it unnecessary; Mathlib lacks it) and any
   "missed elementary route" (would be Eisenstein–Thue, strictly heavier than Route C). The
   ROADMAP's Route-C choice is confirmed correct by this audit.
