# Q1234 (dm3): Mazur cyclic order bound — smallest self-contained module

## Executive answer

For the current axiom

```lean
mazur_cyclic_order_bound
```

which only needs the cyclic exact-order conclusion

```text
if E/ℚ has a rational point P of exact order n, then n ≤ 12 and n ≠ 11,
```

the smallest sensible mathematical payload is **not** the full Mazur torsion-group classification. It is the following two-part exclusion theorem:

1. `no_exact_order_11`: no rational point of exact order `11` on an elliptic curve over `ℚ`.
2. `no_exact_order_ge_13`: no rational point of exact order `n` for any `13 ≤ n`.

Then `mazur_cyclic_order_bound` is only elementary arithmetic:

- `n ≠ 11` follows from `no_exact_order_11`.
- `n ≤ 12` follows by contradiction from `no_exact_order_ge_13`.

So yes: the clean split is

```text
(a) n ≤ 12 branch: only exclude n = 11.
(b) n ≥ 13 branch: this is the actual hard Mazur content.
```

For a Lean project, I would keep the axiom boundary exactly at this split. Formalizing the `n = 11` computation is plausibly small. Formalizing the full `n ≥ 13` branch is not small; it is Mazur-level modular-curve machinery unless one replaces it by a long finite list plus another deep uniform theorem.

## Lean-facing interface sketch

This is an interface sketch, not a proposed compiling patch. It shows the intended mathematical shape of the split. The actual point/order API should be adapted to the local FLT names.

```lean
import Mathlib
import FLT.EllipticCurve.Torsion

namespace FLT.MazurCyclic

-- Schematic: replace `ExactOrder E P n` with the local FLT spelling,
-- probably a statement involving `orderOf P = n` for `P : (E / ℚ).Point`.

axiom no_exact_order_11
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E / ℚ).Point) :
    ¬ ExactOrder P 11

axiom no_exact_order_ge_13
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E / ℚ).Point) (n : ℕ) :
    ExactOrder P n → 13 ≤ n → False

/-- Schematic final theorem: the current `mazur_cyclic_order_bound` payload. -/
theorem mazur_cyclic_order_bound_from_split
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E / ℚ).Point) (n : ℕ)
    (hP : ExactOrder P n) :
    n ≤ 12 ∧ n ≠ 11 := by
  constructor
  · by_contra hn
    exact no_exact_order_ge_13 E P n hP (Nat.succ_le_of_lt (Nat.lt_of_not_ge hn))
  · intro hn
    subst hn
    exact no_exact_order_11 E P hP

end FLT.MazurCyclic
```

## What is genuinely easy?

### Allowed orders do not need proof here

For this axiom, the existence of examples for `n = 1, ..., 10, 12` is irrelevant. We only need an upper/exclusion statement. So do **not** include Kubert parameterizations or existence families in the minimal module unless another theorem needs them.

### Excluding `n = 11` is the smallest self-contained computation

`X_1(11)` is genus `1`. A rational point of exact order `11` gives a non-cuspidal rational point on `X_1(11)`. One can use an explicit elliptic-curve model for `X_1(11)`, compute its Mordell-Weil group over `ℚ`, and check that the rational points are cuspidal. This is a finite genus-one computation: model, rank `0`, torsion, cusp identification.

This is a plausible small formal module compared with Mazur's full theorem.

Recommended theorem boundary:

```text
no_rational_11_torsion:
  ∀ E/ℚ, ∀ P ∈ E(ℚ), exact_order(P) = 11 → False.
```

That theorem proves the `n ≠ 11` half of `mazur_cyclic_order_bound`.

## What happens for `n ≥ 13`?

`X_1(n)` has genus `0` exactly for `n = 1, ..., 10, 12`; these are precisely the cyclic orders that occur infinitely often over `ℚ`. Once `n ≥ 13`, excluding rational exact order `n` is the hard direction. Genus `≥ 2` gives only finiteness of `X_1(n)(ℚ)` by Faltings; it does **not** show that all rational points are cusps. Mazur's proof supplies exactly that missing step, via modular curves, Eisenstein ideals, integral models, and formal immersion arguments.

For individual small `n`, Faltings can be avoided by explicit rational-point computations. But those computations become bespoke high-genus curve computations, not a uniformly small module.

## Divisor-antichain reduction for exact orders

Let

```text
S = {1,2,3,4,5,6,7,8,9,10,12}.
```

If `P` has exact order `n` and `d ∣ n`, then `(n/d)P` has exact order `d`. Therefore, to exclude every `n ∉ S`, it suffices to exclude every **minimal forbidden divisor**.

The minimal forbidden set is

```text
BAD = {p prime | p ≥ 11}
      ∪ {14,15,16,18,20,21,24,25,27,35,49}.
```

Reason: if a bad order has a prime divisor `p ≥ 11`, reduce to exact order `p`. If all prime divisors are in `{2,3,5,7}`, the only integers outside `S` all of whose proper divisors lie in `S` are exactly

```text
14 = 2·7
15 = 3·5
16 = 2^4
18 = 2·3^2
20 = 2^2·5
21 = 3·7
24 = 2^3·3
25 = 5^2
27 = 3^3
35 = 5·7
49 = 7^2
```

This is useful for modularizing the proof. But it also shows why the `n ≥ 13` branch does not reduce to just `13,17,19,...` primes: composite minimal obstructions such as `20`, `24`, `35`, and `49` also have to be ruled out unless one keeps Mazur's theorem as a single hard input.

## Ranked list by proof burden

### Tier 0 — allowed / no exclusion needed

| order `n` | curve `X_1(n)` | status for this axiom |
|---:|---|---|
| `1,2,3,4,5,6,7,8,9,10,12` | genus `0` | allowed; no proof of occurrence needed for the bound |

These should not be part of the minimal proof payload.

### Tier 1 — very small explicit computation

| order `n` | genus of `X_1(n)` | exclusion method | comment |
|---:|---:|---|---|
| `11` | `1` | elliptic curve rank/torsion computation | smallest self-contained module; enough for the `n ≠ 11` half |
| `14` | `1` | elliptic curve rank/torsion computation | easy if decomposing the whole `n ≥ 13` branch into finite cases |
| `15` | `1` | elliptic curve rank/torsion computation | same |

These are the only genus-one bad `X_1(n)` cases. They are the natural first formalization targets if one wants to replace part of Mazur by explicit computations.

### Tier 2 — explicit, but already genus-two machinery

| order `n` | genus of `X_1(n)` | exclusion method | comment |
|---:|---:|---|---|
| `13` | `2` | explicit hyperelliptic rational-point computation, usually via Jacobian rank/descent plus Chabauty or Mordell-Weil sieve | yes, `X_1(13)(ℚ) = cusps` can be checked directly; not just elliptic-curve rank |
| `16` | `2` | same style | needed only if decomposing the full `n ≥ 13` branch |
| `18` | `2` | same style | same |

Answer to the specific question: **yes**, `13` can be avoided as a Mazur black box by an explicit computation on `X_1(13)`. It is still a genus-two rational-points module, not a one-page elliptic-curve computation.

### Tier 3 — explicit in principle, but no longer a small module

| order `n` | genus of `X_1(n)` | likely method | comment |
|---:|---:|---|---|
| `20` | `3` | explicit model plus Chabauty/Mordell-Weil sieve or maps to lower-rank quotients | moderate high-genus computation |
| `17` | `5` | high-genus modular-curve computation | first prime after `13`; not a tiny self-contained proof |
| `21` | `5` | high-genus modular-curve computation | minimal composite obstruction |
| `24` | `5` | high-genus modular-curve computation | minimal composite obstruction |
| `19` | `7` | high-genus modular-curve computation | still individual-computation territory in principle, but heavy |

For these values, one can imagine explicit proof certificates, but formalizing them in Lean would mean formalizing significant algebraic-curve/Jacobian/rational-point infrastructure. That is probably larger than the FLT project wants for this axiom.

### Tier 4 — high-genus finite cases; explicit computation becomes unattractive

| order `n` | genus of `X_1(n)` | comment |
|---:|---:|---|
| `23` prime | `12` | prime case; already high genus |
| `25` | `12` | minimal composite obstruction |
| `27` | `13` | minimal composite obstruction |
| `29` prime | `22` | high genus |
| `35` | `25` | minimal composite obstruction |
| `31` prime | `26` | high genus |
| `37` prime | `40` | special in rational-isogeny theory, but rational torsion still excluded |
| `49` | `69` | minimal composite obstruction, very high genus |

These are not good candidates for a small self-contained formal module. They can be treated by specialized computational arithmetic geometry, but the proof certificates would be large.

### Tier 5 — infinite prime family; genuinely deep uniform content

| family | status |
|---|---|
| primes `p ≥ 23`, and really all primes `p ≥ 17` if not handled individually | requires a uniform theorem; one-by-one explicit computation is not a finite proof |
| all large composite `n` | reduce to either a bad prime divisor or one of the finite composite minimal obstructions above |

This is where Mazur's formal-immersion/Eisenstein-ideal machinery is doing real work. Faltings alone does not solve it: it gives finiteness of `X_1(n)(ℚ)` for each fixed genus-`≥ 2` curve, but not a cusp-only determination, and not a uniform classification across infinitely many `n`.

## Recommended module boundary for FLT

### Best small axiom split

Use two theorem inputs:

```text
No11:
  no exact rational point order 11 over ℚ.

NoGe13:
  no exact rational point order n over ℚ for any n ≥ 13.
```

Then derive the current axiom by arithmetic.

This gives the smallest clean dependency surface:

```text
X1(11) explicit computation  --->  n ≠ 11
Mazur hard large-order part   --->  n ≤ 12
```

### If replacing more of Mazur by explicit computations

The next useful decomposition is:

```text
NoPrimeGe11:
  no exact rational point order p for any prime p ≥ 11.

NoSmallCompositeBad:
  no exact rational point order n for
  n ∈ {14,15,16,18,20,21,24,25,27,35,49}.
```

Together with the divisor-antichain lemma, this proves the cyclic order bound. But `NoPrimeGe11` is still an infinite prime-family theorem, hence essentially Mazur-level unless replaced by another deep uniform bound plus a finite search.

### Practical recommendation

For the FLT Lean development, I would not try to formalize the full rational-points-on-`X_1(n)` story. The smallest maintainable module is:

1. optionally prove/axiomatize `no_exact_order_11` separately, because it is a genuinely finite genus-one computation;
2. keep a single hard theorem/axiom for `no_exact_order_ge_13`;
3. derive `mazur_cyclic_order_bound` from those two inputs.

This preserves the mathematical distinction between the easy finite computation and the real Mazur content without importing the full torsion subgroup classification.

## References for orientation

- Mazur, *Modular curves and the Eisenstein ideal*, Publ. Math. IHÉS 47 (1977), 33–186.
- Mazur, *Rational isogenies of prime degree*, Invent. Math. 44 (1978), 129–162.
- Ogg, *Rational points of finite order on elliptic curves*, Invent. Math. 12 (1971), 105–111.
- Ogg, *Rational points on certain elliptic modular curves*, Proc. Symp. Pure Math. 24 (1973).
- Ligozat, *Courbes modulaires de genre 1*, Bull. Soc. Math. France 103 (1975), 5–80.
- Kubert, *Universal bounds on the torsion of elliptic curves*, Proc. London Math. Soc. 33 (1976), 193–237.
- Derickx and van Hoeij, *Gonality of the modular curve X_1(N)*, J. Algebra 417 (2014), 52–71.
