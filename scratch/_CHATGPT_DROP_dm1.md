# Q93-dm1: scoping `no_rational_point_of_order_ge_17`

## Verdict

There is no Lean/Mathlib-feasible short route to

```lean
no_rational_point_of_order_ge_17
```

short of importing a theorem essentially equivalent to the prime-order part of Mazur's torsion theorem.  This is not like the A4 `Z2×Z14` ex-falso discharge, where the obstruction reduced to a genus-1 rank-zero enumeration on `X_1(14) = 14a4`.  For prime order `p ≥ 17`, the direct modular curve is `X_1(p)`, and all such curves have genus at least `5`.

The smallest honest seam is therefore the theorem itself, or a semantically equivalent modular-curve rational-points theorem.  I would keep the high-level torsion theorem as the named seam, because the repo does not currently have a modular-curve object hierarchy for `X_1(p)`.

```lean
/-- Prime-order part of Mazur's torsion theorem, kept as the final named seam. -/
axiom no_rational_point_of_prime_order_ge_17
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {p : ℕ} (hp : Nat.Prime p) (hp17 : 17 ≤ p)
    (P : (E⧸ℚ).Point)
    (hP : addOrderOf P = p) :
    False
```

A version closer to the existing axiom name could be:

```lean
axiom no_rational_point_of_order_ge_17
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⧸ℚ).Point)
    (hp : Nat.Prime (addOrderOf P))
    (hp17 : 17 ≤ addOrderOf P) :
    False
```

The second is often more convenient if the surrounding code already computes `addOrderOf P`.

---

## 1. Reduction to modular curves

A rational point `P ∈ E(ℚ)` of exact order `p` gives a non-cuspidal rational point on `X_1(p)`.  Forgetting the generator gives a rational cyclic subgroup of order `p`, hence a rational point on `X_0(p)`.

```lean
-- Idealized modular-curve statement, not presently backed by Mathlib objects.
axiom order_p_point_gives_X1p_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {p : ℕ} (hp : Nat.Prime p)
    (P : (E⧸ℚ).Point)
    (hP : addOrderOf P = p) :
    ∃ x : X1 p ℚ, ¬ IsCusp x

axiom X1_prime_ge17_rational_points_are_cusps
    {p : ℕ} (hp : Nat.Prime p) (hp17 : 17 ≤ p)
    (x : X1 p ℚ) :
    IsCusp x
```

These two axioms would imply `no_rational_point_of_prime_order_ge_17`.  But in the current repo, this is not a smaller seam: it requires modular curves, rational cusps, and the moduli interpretation of `X_1(p)`.

The `X_0(p)` route is also not a shortcut by itself.  A rational point of order `p` implies a rational `p`-isogeny, but Mazur's rational isogeny theorem is itself deep.  It says that prime-degree rational isogenies can occur only for

```text
{2, 3, 5, 7, 11, 13, 17, 19, 37, 43, 67, 163}.
```

So `X_0(p)` plus Mazur's isogeny theorem would reduce `p ≥ 17` to the finite set

```text
{17, 19, 37, 43, 67, 163}.
```

But this reduction has merely moved the deep theorem: formalizing Mazur's isogeny theorem is comparable in difficulty to formalizing the relevant part of Mazur's torsion theorem.

---

## 2. Genus of `X_1(p)`

For prime `p ≥ 5`, the genus of `X_1(p)` is

```text
g(X_1(p)) = (p - 5) * (p - 7) / 24.
```

Consequences:

| prime `p` | `g(X_1(p))` | Lean tractability |
|---:|---:|---|
| 5 | 0 | genus 0, parametrized |
| 7 | 0 | genus 0, parametrized |
| 11 | 1 | elliptic curve case |
| 13 | 2 | genus 2, already beyond current Mathlib automation |
| 17 | 5 | high-genus curve |
| 19 | 7 | high-genus curve |
| 23 | 12 | high-genus curve |
| 29 | 22 | high-genus curve |
| 31 | 26 | high-genus curve |
| 37 | 40 | high-genus curve |
| 41 | 51 | high-genus curve |
| 43 | 57 | high-genus curve |
| 47 | 70 | high-genus curve |
| 53 | 92 | high-genus curve |
| 59 | 117 | high-genus curve |
| 61 | 126 | high-genus curve |
| 67 | 155 | high-genus curve |
| 71 | 176 | high-genus curve |
| 73 | 187 | high-genus curve |
| 163 | 1027 | completely out of reach by curve enumeration |

Thus there are **no genus ≤ 1 curves among `X_1(p)` for `p ≥ 17`**.  The first problematic prime in the requested range, `p = 17`, already gives a genus-5 curve.

For comparison, the `X_0(p)` route has smaller genus, and `X_0(17)` and `X_0(19)` are genus-1 curves.  LMFDB lists `X_0(17)` in isogeny class `17.a`; the `Γ_0(N)`-optimal curve is `17.a3` with coefficients `[1, -1, 1, -1, -14]`.  But `X_0(p)` classifies rational cyclic subgroups, not rational generators.  Non-cuspidal rational points on `X_0(17)` and `X_0(19)` do exist; they correspond to rational isogenies, not rational torsion points.

Approximate useful `X_0` status for the exceptional isogeny primes:

| `p` | `g(X_0(p))` | comment |
|---:|---:|---|
| 17 | 1 | LMFDB isogeny class `17.a`; rational 17-isogenies exist |
| 19 | 1 | LMFDB isogeny class `19.a`; rational 19-isogenies exist |
| 37 | 2 | rational 37-isogenies exist; still not rational 37-torsion |
| 43 | 3 | exceptional rational isogeny prime |
| 67 | 5 | exceptional rational isogeny prime |
| 163 | 13 | exceptional rational isogeny prime |

This is why `X_0` does not give an A4-style rank-zero contradiction for the torsion problem.

---

## 3. Uniform Mazur method vs curve-by-curve

A curve-by-curve proof on `X_1(p)` is not near-term feasible.  It would require infinitely many primes unless one first proves a finite reduction such as Mazur's isogeny theorem or another uniform boundedness theorem.  The finite `X_0` exceptional list is itself produced by Mazur's method.

The actual uniform proof uses the arithmetic of modular curves and their Jacobians: Eisenstein ideals, cuspidal subgroups, Hecke algebras, winding quotients, reduction at primes, and formal immersion arguments.  This is more elegant mathematically than enumerating rational points on huge `X_1(p)`, but it is **not** currently more formalizable in Mathlib.  It would require a large modular-curves/Jacobians/Hecke-algebra infrastructure that the repo does not have.

A stylized Lean target for the uniform method would look like:

```lean
-- Not currently realistic without a substantial modular-curves library.
axiom Mazur_Eisenstein_prime_torsion_obstruction
    {p : ℕ} (hp : Nat.Prime p) (hp17 : 17 ≤ p)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⧸ℚ).Point)
    (hP : addOrderOf P = p) :
    False
```

This is intentionally almost identical to the high-level seam, because exposing the internal modular-curve proof structure would create many deeper seams rather than fewer.

---

## 4. True Mathlib blockers

The blockers are not small polynomial identities.  They are foundational arithmetic geometry components:

1. **Modular curves as objects over `ℚ`**: definitions of `X_1(N)`, `X_0(N)`, cusps, rational points, and moduli interpretations.
2. **Maps from elliptic torsion data to modular curves**: a formal construction turning `P : E(ℚ)` with `addOrderOf P = p` into a noncuspidal point on `X_1(p)(ℚ)`.
3. **High-genus rational point tools**: models, divisors, Jacobians, Abel-Jacobi maps, Mordell-Weil groups, Chabauty-Coleman, Mordell-Weil sieve, or equivalent certified rational-point enumeration.
4. **Mazur's uniform method**: Jacobians `J_0(p)`, Hecke algebras, Eisenstein ideals, cuspidal subgroup calculations, formal immersion at cusps, and reduction arguments.

Mathlib has strong algebra, finite group theory, polynomial/resultant infrastructure, and growing elliptic-curve Weierstrass APIs.  It does not currently have enough of the above to make this seam closeable.

---

## 5. Recommended seam shape in `flt-ai`

Keep the seam at the theorem level:

```lean
namespace FLT.MazurPrimeTorsion

/--
Final named seam: prime-order part of Mazur's torsion theorem over `ℚ`.

This is deliberately stronger than any modular-curve-specific statement, because the
current repo does not have `X_1(p)`/`X_0(p)` as formal objects.
-/
axiom no_rational_point_of_prime_order_ge_17
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {p : ℕ} (hp : Nat.Prime p) (hp17 : 17 ≤ p)
    (P : (E⧸ℚ).Point)
    (hP : addOrderOf P = p) :
    False

/-- Convenience wrapper if the order is already known to be prime. -/
theorem no_prime_order_ge_17_of_addOrderOf
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⧸ℚ).Point)
    (hp : Nat.Prime (addOrderOf P))
    (hp17 : 17 ≤ addOrderOf P) :
    False := by
  exact no_rational_point_of_prime_order_ge_17
    E hp hp17 P rfl

end FLT.MazurPrimeTorsion
```

Depending on how your current axiom is stated, you may want the axiom itself in the `addOrderOf` form to avoid rewriting through a separate prime parameter.

---

## 6. Ranking against the other hard seams

This seam is deeper than the previous named seams:

```text
SEAM2 x-coordinate formula: hard but algebraic/closeable.
SEAM1 division-polynomial separability: deep local/formal geometry seam.
X1(16) rational points: genus-2 rational-points seam.
Prime p ≥ 17 torsion exclusion: heart of Mazur; deeper than all of the above.
```

So the right engineering decision is to keep `no_rational_point_of_order_ge_17` as the single named Mazur-prime seam and move on.  Splitting it into modular-curve pieces would be mathematically cleaner only after the repo has a real modular-curve/Jacobian layer.

---

## References checked

* Mazur isogeny theorem prime list: Philippe Michaud-Jacobs, *Mazur's isogeny theorem*, arXiv:2209.03153.
* Genus formulas for modular curves including `X_1(N)`: Hamakiotes--Lau, *Genus formulas for families of modular curves*, arXiv:2501.10883.
* LMFDB isogeny class `17.a`, including the `Γ_0(N)`-optimal curve `17.a3` with coefficients `[1,-1,1,-1,-14]`.
* Standard modular-curve genus summaries: tables for `X_0(N)` genus-one cases and the genus-zero list for `X_1(n)`.
