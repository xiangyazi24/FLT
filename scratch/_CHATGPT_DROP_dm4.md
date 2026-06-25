# Q284 (dm4): can Mathlib already prove `preΨ'ₙ` separability by torsion counting?

## Executive answer

The proposed shortcut is mathematically reasonable on paper, but it is **not** a clean Lean shortcut with the current ingredients, and it is very likely circular in this project.

The route

```text
degree(preΨ'ₙ) = expected d
+ preΨ'ₙ splits over alg-closed k
+ roots are exactly non-2 n-torsion x-coordinates
+ there are exactly d distinct such x-coordinates
⇒ all roots are simple
⇒ preΨ'ₙ separable
```

requires a non-circular theorem that the geometric `n`-torsion has exactly the expected rank/cardinality:

```text
E[n](k) ≃ (Z/nZ)^2,
#E[n](k) = n^2,
```

or at least the distinct x-coordinate count after quotienting by `±1`.  That theorem is essentially the same geometric separability/étaleness content as the separability of the multiplication-by-`n` kernel.  Unless it has been independently formalized from the formal group/tangent argument `d[n] = n`, using it to prove division-polynomial separability just moves the same bridge somewhere else.

So the safe conclusion is:

* `natDegree_preΨ'` is useful for the degree side.
* `IsAlgClosed` gives splitting.
* `mk_ψ`, `mk_φ`, `mk_Ψ_sq` help identify kernels with division-polynomial zero loci.
* But Mathlib does **not** appear to provide the full independent rank-two torsion theorem needed to count roots.
* Any repo theorem named like `geomNTorsion_rank_two_linear` must be dependency-audited.  If it imports/uses `preΨ'_separable`, `preΨ'_eval_eq_zero_iff_exists_non_two_torsion`, the E1 bridge, or a theorem proved from the keystone torsion-cardinality seam, it is circular for this purpose.

## Repository check caveat

I attempted to search the accessible `xiangyazi24/FLT` GitHub index for names like

```text
geomNTorsion_rank_two_linear
preΨ'_separable
rank_two
n_torsion_finite
```

and got no hits.  The connector also did not expose the `ai-scratch` branch/files in this session, so I could not directly inspect `scratch/KeystoneNTorsion.lean` or any theorem with that exact name.  The dependency conclusion below is therefore an architectural one: even if such a theorem exists locally, it must be treated as usable for this shortcut only if its imports/proof do **not** depend on the division-polynomial separability bridge you are trying to prove.

## Why the counting proof is not currently a shortcut

To make the counting proof work, you need the following exact chain.

```lean
-- schematic only
have hdeg : (W.preΨ' n).natDegree = expectedDegree n :=
  WeierstrassCurve.natDegree_preΨ' ...

have hsplit : (W.preΨ' n).Splits (RingHom.id k) := by
  -- from [IsAlgClosed k]
  exact Polynomial.splits_of_isAlgClosed _

have hroots_exact :
    {x | (W.preΨ' n).eval x = 0}
      = {x | ∃ y h, 2 • P(x,y,h) ≠ 0 ∧ n • P(x,y,h) = 0} := by
  -- this is exactly the theorem currently under construction:
  -- preΨ'_eval_eq_zero_iff_exists_non_two_torsion
  sorry

have hcard_xroots :
    Fintype.card {x // (W.preΨ' n).eval x = 0} = expectedDegree n := by
  -- requires E[n] ≃ (ZMod n × ZMod n), then quotient by ±P and remove 2-torsion.
  sorry
```

The problem is the last two steps:

1. `hroots_exact` is already one of the downstream bridge results.  If it uses `preΨ'` separability, it cannot be used to prove separability.
2. `hcard_xroots` is not available from mere finiteness.  `n_torsion_finite` only gives finite, not the expected cardinality or rank-two structure.

Classically, the theorem `E[n](k) ≃ (Z/nZ)^2` for `char k ∤ n` is proved using the fact that `[n]` is a separable isogeny of degree `n^2`, or equivalently that its kernel is finite étale of rank `n^2`.  The separability of `[n]` is proved from the differential `d[n] = n`, i.e. the same formal-group tangent input you identified in bridge-2.  That is fine as an independent route, but then the formalized theorem must expose that proof directly.  If the theorem was instead proved by division polynomials, it is circular here.

## What to grep in the local branch

Run these locally on `ai-scratch`:

```bash
grep -R "geomNTorsion_rank_two_linear" -n .
grep -R "rank_two" -n scratch FLT Mathlib | head -100
grep -R "preΨ'_separable\|preΨ'_eval_eq_zero_iff_exists_non_two_torsion\|deriv_ne_zero\|separable" -n scratch/KeystoneNTorsion.lean FLT/EllipticCurve/Torsion.lean scratch | head -200
```

For any candidate theorem, inspect its import chain:

```bash
grep -n "^import" scratch/KeystoneNTorsion.lean
grep -n "preΨ'_separable\|preΨ'_eval_eq_zero_iff_exists_non_two_torsion\|SeamE1\|Torsion" scratch/KeystoneNTorsion.lean
```

A theorem like this is **usable** for the shortcut only if it is proved without importing or using:

```text
preΨ'_separable
preΨ'_derivative_ne_zero_at_roots
preΨ'_eval_eq_zero_iff_exists_non_two_torsion
nsmul_eq_zero_iff_preΨ'_eval_eq_zero_of_two_nsmul_ne_zero
any theorem whose proof uses those
```

It is **circular** if it depends on the torsion/division-polynomial root equivalence or the separability theorem under construction.

## How the shortcut would look if a non-circular rank-two theorem exists

If you really have an independent theorem of this form:

```lean
-- schematic
noncomputable def torsionEquivRankTwo
    (W : WeierstrassCurve k) [W.IsElliptic]
    [IsAlgClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    {P : (W⁄k).Point // n • P = 0} ≃ (ZMod n × ZMod n)
```

and a non-circular root equivalence:

```lean
-- schematic
(W.preΨ' n).eval x = 0 ↔
  ∃ y h, 2 • Point.some x y h ≠ 0 ∧ n • Point.some x y h = 0
```

then the separability proof can be done by cardinality:

```lean
-- schematic only
theorem preΨ'_separable_by_torsion_count
    (W : WeierstrassCurve k) [W.IsElliptic]
    [IsAlgClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).Separable := by
  -- 1. get `natDegree_preΨ'`.
  have hdeg := WeierstrassCurve.natDegree_preΨ' (W := W) (n := n) hn

  -- 2. all roots split over `k`.
  have hsplit : (W.preΨ' n).Splits (RingHom.id k) := by
    exact Polynomial.splits_of_isAlgClosed _

  -- 3. identify roots with non-2 n-torsion x-coordinates.
  have hroot_equiv := preΨ'_root_xcoord_equiv_non_two_torsion_xcoords
    (W := W) (n := n) hn

  -- 4. count those x-coordinates from independent rank-two torsion.
  have hcard_roots :
      Fintype.card {x : k // (W.preΨ' n).eval x = 0}
        = (W.preΨ' n).natDegree := by
    -- rank-two torsion count, remove `O` and 2-torsion if needed,
    -- quotient non-2 points by `P ~ -P`; the quotient map is exactly `x`.
    sorry

  -- 5. use a standard split-polynomial criterion:
  -- if a split nonzero polynomial has as many distinct roots as its degree,
  -- then it is squarefree/separable.
  exact separable_of_splits_card_roots_eq_natDegree hsplit hcard_roots
```

But this is not shorter unless steps 3 and 4 are already non-circularly available.  In the current architecture, step 3 is precisely the sub-D theorem you are closing, and step 4 is usually proved from the same étaleness/separability input.

## Recommendation

Do **not** switch to the torsion-counting proof unless you can exhibit a theorem, already in the local branch, whose proof of geometric `n`-torsion rank two/order `n^2` depends only on:

```text
formal group / tangent map `d[n] = n`,
isogeny degree theory independent of division-polynomial separability,
or a pre-existing Mathlib theorem about finite étale kernels of elliptic curves
```

and not on the `preΨ'` separability bridge.

Given the current state described in the previous atoms, the formal-group/local-parameter bridge remains the correct non-circular path.  It proves the derivative nonvanishing directly from `d[n] = n` and the projective division-polynomial formula, instead of trying to count torsion roots with a theorem whose proof likely already uses the desired separability.
