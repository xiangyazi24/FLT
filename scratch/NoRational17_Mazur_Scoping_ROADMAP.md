
═══ BRIDGE SUBMITTED  dm2 | task 235b3ed9 | 1709B in | "Q10 (dm2): Lean 4 / Mathlib. flt-ai. SCOPING the deepest pil…" ═══

[ask-gpt dm2 tid=235b3ed9 +0s] dispatched, waiting for answer
[ask-gpt dm2 tid=235b3ed9 +90s] waiting (status=processing)
[ask-gpt dm2 tid=235b3ed9 +180s] waiting (status=processing)
[ask-gpt dm2 tid=235b3ed9 +270s] waiting (status=processing)
[ask-gpt dm2 tid=235b3ed9 +360s] waiting (status=processing)
[ask-gpt dm2 tid=235b3ed9 +446s] terminal: status=completed

═══ BRIDGE RUN #39  dm2 | task 235b3ed9 | 8284 B | ✅ COMPLETE ═══

## Verdict

`no_rational_point_of_order_ge_17` is essentially the **cyclic half of Mazur’s torsion theorem**, not a finite handful of N10/N12-style computations. It is an **infinite family** of modular-curve rational-point exclusions:

```text
∀ N ≥ 17,  Y₁(N)(ℚ) = ∅
```

equivalently, every `X₁(N)(ℚ)` point is cuspidal. Mathlib/FLT currently has no modular-curve/Eisenstein-ideal infrastructure that would make this reachable. In FLT, Mazur’s torsion bound is still represented by an axiom `Mazur_statement`, with comments explicitly describing Mazur’s theorem and the torsion bound ≤16. fileciteturn61file0L35-L41 fileciteturn61file0L105-L108

## 1. Is this finite curve-by-curve or uniform Mazur machinery?

A rational point `P : E(ℚ)` of exact order `N` gives a noncuspidal rational point on `Y₁(N)`, hence on `X₁(N)`. The modular-curve page describes `X₁(N)` as the modular curve whose level structure is a point of order `N`; it also notes that `X₁(n)` has genus zero exactly for `n = 1,…,10,12`, and that the converse assertion “only these `n` occur over ℚ” is Mazur’s torsion theorem. citeturn959904search4

For `N ≥ 17`, the curves `X₁(N)` are already genus ≥ 2. Using the standard Γ₁ genus formula, the first few are:

```text
N    genus X₁(N)
17   5
18   2
19   7
20   3
21   5
22   6
23   12
24   5
25   12
26   10
27   13
28   10
29   22
30   9
31   26
32   17
```

So there is no “rank-zero elliptic curve for each `N`” story. Starting at 17, these are genus ≥ 2 rational-point problems. Faltings gives finiteness for each fixed genus ≥ 2 curve, but not an effective list of points; the rational-point page also notes that for genus ≥ 2 there is no known general algorithm that always determines all rational points. citeturn904375search2turn371699search5

There is no finite set of divisibility checks that catches every order `N ≥ 17`: if `N` is a prime `p ≥ 17`, then a point of order `p` has no smaller forbidden divisor besides `p` itself. Thus, unless you import a uniform theorem, you face infinitely many prime levels.

## 2. Is there a uniform argument?

Yes mathematically: **Mazur’s theorem** is the uniform argument. But it is not a lightweight genus/gonality bound. It uses modular curves, modular Jacobians, Eisenstein ideals, and arithmetic of modular forms/Jacobians. The FLT comments accurately describe Mazur’s theorem as classifying possible rational torsion groups and explain that every known proof of FLT uses this result. fileciteturn61file0L35-L43

There are later uniform-boundedness theorems, such as Merel’s theorem over number fields, but these are even broader and no more Mathlib-accessible for this purpose. A gonality result can prove structural finiteness or bounds in some settings, but it does not by itself identify `X₁(N)(ℚ)` with the cusps for all `N ≥ 17`; Derickx–van Hoeij compute gonality of `X₁(N)` for `N ≤ 40` and upper bounds up to `250`, which is useful computational arithmetic geometry, not a replacement for Mazur in Lean. citeturn904375academia6

So the realistic Lean route is not:

```text
prove X₁(17)(ℚ), X₁(18)(ℚ), X₁(19)(ℚ), ... curve by curve
```

It is either:

```text
formalize Mazur’s theorem / Eisenstein ideal machinery
```

or keep this as a named pillar axiom.

## 3. Depth compared with `mordell_weil_fg`

`no_rational_point_of_order_ge_17` is, in formalization terms, at least as deep as the cyclic part of Mazur’s theorem. It is not comparable to N10/N12 explicit descents. It is much closer to “formalize a large part of arithmetic geometry of modular curves.”

`mordell_weil_fg` is also a major theorem: it needs heights, descent, weak Mordell-Weil, Selmer/Kummer finiteness, and arithmetic of number fields. But it is a classical structural theorem about elliptic curves over number fields. Mazur’s theorem is later and deeper: it uses modular curves and modular Jacobians. The FLT `Mazur.lean` file’s discussion emphasizes that Mazur’s proof is a 154-page modular-curve/Eisenstein-ideal argument. fileciteturn61file0L43-L57

My honest Lean tractability ranking:

```text
N10 / N12 explicit obstruction curves     tractable, project-local
N14 via X₁(14)=14a4                       tractable if cyclic-14 already done
N16 via X₁(16) genus 2                    deep but bounded/specific
mordell_weil_fg                           very large theorem
no_rational_point_of_order_ge_17          Mazur-level, broader/deeper than one curve
full Mazur torsion classification         deepest current pillar here
```

So `no_rational_point_of_order_ge_17` is **not** a multi-N finite checklist. It is effectively a named piece of Mazur.

## 4. Do we need all `N ≥ 17` to get `|T| ≤ 16`?

To rule out cyclic torsion of order `> 16`, yes, you need exactly a statement of this strength:

```lean
∀ P : (E⁄ℚ).Point, addOrderOf P ≤ 16
```

or equivalently:

```lean
¬ ∃ P : (E⁄ℚ).Point, 17 ≤ addOrderOf P
```

That only controls the **exponent** of the torsion group. It is not enough by itself to prove `|T| ≤ 16`, because groups like `ℤ/2 × ℤ/16` have exponent `16` but order `32`. That is why the rank-two exclusions such as `Z/2 × Z/N` for `N = 10,12,14,16` are separate. In your architecture, the bound `|T|≤16` needs both:

```text
A. no cyclic point order ≥ 17
B. no large rank-two torsion configurations, especially Z/2 × Z/N for N=10,12,14,16
```

A cheaper sufficient theorem for the cyclic part is just the exponent form:

```lean
theorem rational_torsion_exponent_le_16
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ P : (E⁄ℚ).Point, addOrderOf P ≤ 16
```

This is equivalent to your current axiom up to elementary `Nat` reasoning:

```lean
theorem no_ge17_iff_exponent_le16
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (¬ ∃ P : (E⁄ℚ).Point, 17 ≤ addOrderOf P) ↔
      ∀ P : (E⁄ℚ).Point, addOrderOf P ≤ 16 := by
  constructor
  · intro h P
    by_contra hle
    have h17 : 17 ≤ addOrderOf P := by omega
    exact h ⟨P, h17⟩
  · intro h ⟨P, h17⟩
    have := h P
    omega
```

But this is not mathematically cheaper; it is just a better-shaped axiom for group theory.

If your ultimate theorem is literally only:

```lean
(AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16
```

then the **cheapest sufficient statement** is exactly FLT’s current `Mazur_statement` axiom. fileciteturn61file0L105-L108 It bypasses cyclic/rank-two decomposition entirely. If you want to decompose Mazur into more explicit pieces, then `no_rational_point_of_order_ge_17` remains the infinite/uniform cyclic piece.

## Concrete Lean architecture

I would keep the axiom named and isolated as:

```lean
theorem cyclic_torsion_order_le_16
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ P : (E⁄ℚ).Point, addOrderOf P ≤ 16 := by
  -- exactly equivalent to no_rational_point_of_order_ge_17
  ...
```

Then downstream group theory should depend on this, not on explicit `X₁(N)` objects.

For the cyclic modular-curve formulation, the missing API would be something like:

```lean
-- not present in Mathlib
def ModularCurve.X1 (N : ℕ) : Scheme

def Y1_nonCuspidalPointOfTorsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = N) :
    (ModularCurve.X1 N).RatPoint

theorem X1_rational_points_cuspidal_of_ge17
    {N : ℕ} (hN : 17 ≤ N) :
    ∀ Q : (ModularCurve.X1 N).RatPoint, IsCusp Q
```

Mathlib does not currently have this modular-curve layer. It does have Weierstrass curves and point group laws, and FLT has `WeierstrassCurve.nTorsion` and Galois-representation scaffolding, but the modular-curve/Jacobian/Eisenstein machinery is not there. fileciteturn62file0L33-L44 fileciteturn62file0L98-L119

## Recommended scoping decision

Do **not** try to discharge `no_rational_point_of_order_ge_17` by explicit N-level obstruction curves. It is an infinite family and effectively the cyclic Mazur theorem.

For now, use one of these two seams:

```lean
-- broadest, already in FLT
axiom Mazur_statement :
  (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16

-- narrower cyclic seam
axiom cyclic_torsion_order_le_16 :
  ∀ P : (E⁄ℚ).Point, addOrderOf P ≤ 16
```

The narrower seam is nicer if you are separately proving rank-two exclusions. But it is still a Mazur-level theorem, not a bounded finite computation.
