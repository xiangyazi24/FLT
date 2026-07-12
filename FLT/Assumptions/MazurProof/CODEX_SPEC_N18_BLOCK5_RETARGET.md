# N18 Block-5 RETARGET (Fable-diagnosed) — STOP the Newton-polygon grind

The 3-adic separatedness for the SUPERSINGULAR reduction of E₀=162.c3 at π=a−1 over
L=ℚ(ζ₉)⁺ does NOT need the `[3]`-series Newton polygon / z⁹ leading-term valuation. That
grind is aimed at the wrong object (and at a FALSE statement — see ⚠️). Retarget to three
independent lemmas, none of which touches the multiplication-series leading term:

## ⚠️ Do NOT try to prove "a nonzero formal point is not 3-torsion" — it is FALSE here.
Supersingular reduction ⇒ E₀[3^∞] is connected ⇒ the order-3 point T reduces INTO the formal
kernel, so T IS a nonzero formal 3-torsion point. The correct exclusion target is ORDER-9, not
3-torsion. Also: you cannot derive "z not 3-torsion" from a LOWER bound (if [3]z=0 then
v([3]z)=∞ ≥ min{…} vacuously).

## Lemma A — no prime-to-3 torsion (ONE line, zero valuations)
For m with 3∤m: m is a unit in 𝒪_{L,π} (residue char 3). So `[m](T) = m·T + O(T²)` has a UNIT
linear coefficient ⇒ it has a compositional inverse in 𝒪[[T]] (formal inverse-function theorem)
⇒ `[m]` is an AUTOMORPHISM of Ê₀(𝔪_L) ⇒ injective ⇒ no nonzero m-torsion. Height/ordinary/
supersingular is IRRELEVANT; the only fact used is 3∤m ⇒ m ∈ 𝒪^×. This is the ENTIRE "no
prime-to-3 torsion" goal. **First check Mathlib** for: power-series compositional inverse when
f(0)=0 ∧ f'(0)∈𝒪^× (PowerSeries inverse / formal-group `[m]` invertibility) before building it.

## Lemma B — 𝔪²-torsion-free (the ONE genuine deep input; PACKAGE it)
Formal logarithm gives `log : Ê₀(𝔪ⁿ) ≅ (𝔪ⁿ, +)` for `n > e/(p−1)`. Here e = v(3) = 3, p = 3,
so e/(p−1) = 3/2 and **n = 2 works**. Hence Ê₀(𝔪²) ≅ (𝔪², +), which is torsion-free. This is
Silverman AEC IV.6.4(b), height-agnostic. If Mathlib lacks the formal-log iso, **package it as
ONE named hypothesis** (interface-field pattern, e=3, n=2) — do NOT grind p-adic log
convergence blind.

## Lemma C — 3-power torsion has exponent 3 (short valuation step, uses B)
Any nonzero torsion point z lies in 𝔪∖𝔪² (by B) ⇒ v(z)=1. Then `[3]z = 3z + z²A(z)` gives
`v([3]z) ≥ min{v(3)+v(z), 2v(z)} = min{4, 2} = 2`, so [3]z ∈ 𝔪². If z had order 9, [3]z would
be a NONZERO order-3 point ⇒ torsion ⇒ v=1, contradicting v([3]z) ≥ 2. So every 3-power
torsion point is killed by [3].

## Assemble → [21]-annihilator
A + C ⇒ formal-kernel torsion = exactly the 3-torsion, exponent 3. The "7" in [21] is NOT a
3-adic fact: it is the prime-to-3 residue bound at a SECOND good prime 𝔮 — a decidable
`#Ẽ₀(𝔽_𝔮)` computation, made valid BY Lemma A's reduction-injectivity. Keep it as a separate
cheap decidable goal; do not entangle it with the formal-group work.

## Sanity-check two premises the block rests on
(i) E₀ genuinely has GOOD supersingular reduction at π over L (not merely potentially-good /
additive). (ii) e = v(3) = 3 with v(π) = 1. If reduction at π is only potentially good, Lemma
B's e changes and the n-threshold shifts.

## Net
Unblock = RETARGET, not more arithmetic. A is trivial; C is two lines on top of B; B is the one
honest deep input to package. The supersingular height-2 series that has eaten hours is
irrelevant to all of it.
