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

## Route-2 backup (parked)

The E₀ rank-0 route (`FormalKernel18`/`N18Block5Instantiation`, add_congr, front_end) is
architecturally complete but carries the flagged Mathlib gap (Package II formal-log iso,
`Ê₀(𝔪²)` torsion-free). Scouting dispatched to flt4 (formal-log Mathlib) + flt5 (add_congr).
Only revive if Route-1 descent proves intractable.
