# Q258-dm1: doubling half of the keystone EDS core

## Connector status

I attempted to fetch the files named in the prompt from the connected repository/branch:

```text
xiangyazi24/FLT, branch scratch
scratch/DoublingTest.lean
scratch/WardSomos.lean
scratch/PsiSomos.lean
```

The GitHub connector returned `404 Not Found` for these paths on branch `scratch`.  Because of that, I cannot truthfully claim the code below was pasted into the exact local skeleton and build-checked against the actual local theorem names/import paths.

What follows is therefore the tightest honest Lean template for the doubling half, written to use precisely the facts stated in the prompt:

```lean
FLT.EDS.normEDS_adjacent_somos
psi_adjacent_somos
mk_psi_adjacent_somos
```

The remaining issue is not mathematical depth anymore; it is obtaining the exact local names and the residual normal form in `DoublingTest.lean`.

---

## The theorem to prove

```lean
import Mathlib
-- Replace these imports by the actual local imports once the scratch files are visible.
-- import scratch.WardSomos
-- import scratch.PsiSomos

open Polynomial WeierstrassCurve

namespace FLT.DivisionPolynomialDoubling

variable {R : Type*} [CommRing R]

noncomputable def dupNumP (W : WeierstrassCurve R) (P Q : R[X]) : R[X] :=
  P ^ 4
    - C W.b₄ * P ^ 2 * Q ^ 2
    - C (2 * W.b₆) * P * Q ^ 3
    - C W.b₈ * Q ^ 4

noncomputable def dupDenP (W : WeierstrassCurve R) (P Q : R[X]) : R[X] :=
  C 4 * P ^ 3 * Q
    + C W.b₂ * P ^ 2 * Q ^ 2
    + C (2 * W.b₄) * P * Q ^ 3
    + C W.b₆ * Q ^ 4

end FLT.DivisionPolynomialDoubling
```

---

## Descent lemma: `mk ∘ C` is injective

Use the coordinate-ring basis.  The exact Mathlib lemma name used in previous scoping was

```lean
WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero
```

If your checkout has the basis theorem under a different name, replace that line only.

```lean
namespace FLT.DivisionPolynomialDoubling

open WeierstrassCurve.Affine
open WeierstrassCurve.Affine.CoordinateRing

variable {R : Type*} [CommRing R]

/-- Constants in `Y`, i.e. elements of `R[X]`, inject into the affine coordinate ring. -/
theorem mk_C_eq_zero
    (W : WeierstrassCurve.Affine R)
    {p : R[X]}
    (h : mk W (Polynomial.C p) = 0) :
    p = 0 := by
  have hlin :
      p • (1 : W.CoordinateRing)
        + (0 : R[X]) • (mk W Polynomial.X) = 0 := by
    -- `Polynomial.C p` maps to `p • 1` in the coordinate ring.
    simpa [WeierstrassCurve.Affine.CoordinateRing.smul] using h
  exact (WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero hlin).1

/-- Descent from coordinate-ring equality of constants in `Y` to equality in `R[X]`. -/
theorem mk_C_injective
    (W : WeierstrassCurve.Affine R) :
    Function.Injective (fun p : R[X] => mk W (Polynomial.C p)) := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply mk_C_eq_zero W
  have hsub : mk W (Polynomial.C p) - mk W (Polynomial.C q) = 0 := by
    simpa [hpq]
  simpa [map_sub] using hsub

end FLT.DivisionPolynomialDoubling
```

If this descent lemma fails to compile, the minimal replacement seam is:

```lean
axiom mk_C_injective
    {R : Type*} [CommRing R]
    (W : WeierstrassCurve.Affine R) :
    Function.Injective (fun p : R[X] =>
      WeierstrassCurve.Affine.CoordinateRing.mk W (Polynomial.C p))
```

This is a small algebra fact: the affine coordinate ring is free over `R[X]` with basis `{1,Y}` because the Weierstrass equation is monic quadratic in `Y`.

---

## Coordinate-ring proof skeleton

The strategy is correct:

1. Map the raw polynomial difference into the coordinate ring by `mk ∘ C`.
2. Rewrite `mk(C Φ n)` as `mk(φ n)` using `mk_φ`.
3. Rewrite `mk(C ΨSq n)` as `mk(ψ n)^2` using `mk_Ψ_sq` and `mk_ψ`.
4. Expand the `φ` definitions and the even/odd `ψ` recurrences.
5. Use `mk_psi_adjacent_somos W m` to kill the residual.
6. Descend by `mk_C_injective`.

The following theorem is the exact shape I would use.  The one line that must be adapted to the local file is the final `polyrith`/`linear_combination` block, because it depends on the actual normal form left by `DoublingTest.lean`.

```lean
namespace FLT.DivisionPolynomialDoubling

open Polynomial WeierstrassCurve
open WeierstrassCurve.Affine
open WeierstrassCurve.Affine.CoordinateRing

variable {R : Type*} [CommRing R]
variable (W : WeierstrassCurve R)

/-- Raw polynomial difference for the doubling identity. -/
noncomputable def dupCrossDiff (m : ℤ) : R[X] :=
  W.Φ (2 * m) * dupDenP W (W.Φ m) (W.ΨSq m)
    - W.ΨSq (2 * m) * dupNumP W (W.Φ m) (W.ΨSq m)

/-- Coordinate-ring version of the doubling cross identity. -/
theorem mk_dup_doubling_cross (m : ℤ) :
    mk W.toAffine (Polynomial.C (dupCrossDiff W m)) = 0 := by
  classical

  -- Rewrite target into an equality in the coordinate ring.
  unfold dupCrossDiff dupNumP dupDenP

  -- Orient the coordinate-ring congruences.
  -- These are the facts stated in the prompt.
  have hφ_m :
      mk W.toAffine (W.φ m) = mk W.toAffine (Polynomial.C (W.Φ m)) :=
    WeierstrassCurve.Affine.CoordinateRing.mk_φ W m
  have hφ_2m :
      mk W.toAffine (W.φ (2 * m)) = mk W.toAffine (Polynomial.C (W.Φ (2 * m))) :=
    WeierstrassCurve.Affine.CoordinateRing.mk_φ W (2 * m)

  have hψ_m :
      mk W.toAffine (W.ψ m) = mk W.toAffine (W.Ψ m) :=
    WeierstrassCurve.Affine.CoordinateRing.mk_ψ W m
  have hψ_2m :
      mk W.toAffine (W.ψ (2 * m)) = mk W.toAffine (W.Ψ (2 * m)) :=
    WeierstrassCurve.Affine.CoordinateRing.mk_ψ W (2 * m)

  have hΨSq_m :
      mk W.toAffine (W.Ψ m) ^ 2 = mk W.toAffine (Polynomial.C (W.ΨSq m)) :=
    WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq W m
  have hΨSq_2m :
      mk W.toAffine (W.Ψ (2 * m)) ^ 2 = mk W.toAffine (Polynomial.C (W.ΨSq (2 * m))) :=
    WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq W (2 * m)

  have hψ2sq :
      mk W.toAffine W.ψ₂ ^ 2 = mk W.toAffine (Polynomial.C W.Ψ₂Sq) :=
    WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq W

  -- The new lemma from `scratch/PsiSomos.lean`.
  have hS := mk_psi_adjacent_somos (W := W) (m := m)

  -- From here the proof is a pure polynomial identity in the coordinate ring.
  -- The robust close is:
  --   1. Rewrite all `mk(C Φ)` and `mk(C ΨSq)` using the facts above.
  --   2. Expand `φ` and the relevant `ψ` recurrences.
  --   3. Use `hS` as the single nontrivial relation.
  --
  -- In a local file where `mk_psi_adjacent_somos` and the recurrences are visible,
  -- the intended close is one of the following two blocks.

  -- First try this.  `polyrith` is the best tactic for exactly this situation:
  -- a nonlinear polynomial goal over a commutative ring with one or more equality hypotheses.
  all_goals
    try
      simp [map_add, map_sub, map_mul, map_pow,
        hφ_m.symm, hφ_2m.symm,
        hψ_m.symm, hψ_2m.symm,
        hΨSq_m.symm, hΨSq_2m.symm,
        hψ2sq.symm,
        WeierstrassCurve.φ,
        WeierstrassCurve.ψ,
        WeierstrassCurve.ΨSq,
        WeierstrassCurve.Φ,
        WeierstrassCurve.Ψ₂Sq,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈] at hS ⊢

  -- If the previous simp normalizes the goal and `hS`, this should close.
  -- If not, replace by the generated `linear_combination` certificate described below.
  polyrith
```

### If `polyrith` does not close

Replace the last line by a generated certificate:

```lean
  linear_combination (norm := ring_nf)
    Csomos * hS
      + Cb8 * (by
          -- `4*b₈ = b₂*b₆ - b₄^2`, mapped into the coordinate ring.
          -- Depending on the local statement of `b_relation`, orient it here.
          sorry)
```

The only cofactor that is not always needed is `Cb8`: if `simp` unfolds the `bᵢ` invariants to `aᵢ`, then `ring_nf` handles it; if it keeps `b₂,b₄,b₆,b₈` abstract, add the mapped `b_relation` equality.

The cofactor generation script is:

```python
# Sage script to generate the replacement for `polyrith`.
R = PolynomialRing(QQ, names='A,B,C,D,E,Q,T,X,b2,b4,b6,b8', order='degrevlex')
A,B,C,D,E,Q,T,X,b2,b4,b6,b8 = R.gens()

# A=ψ(m-2), B=ψ(m-1), C=ψ(m), D=ψ(m+1), E=ψ(m+2)
# Q=ψ₂², T=Ψ₃ / ψ₃ as it appears in mk_psi_adjacent_somos

Qpoly = 4*X^3 + b2*X^2 + 2*b4*X + b6
Tpoly = 3*X^4 + b2*X^3 + 3*b4*X^2 + 3*b6*X + b8

def dupNum(P,Z):
    return P^4 - b4*P^2*Z^2 - 2*b6*P*Z^3 - b8*Z^4

def dupDen(P,Z):
    return 4*P^3*Z + b2*P^2*Z^2 + 2*b4*P*Z^3 + b6*Z^4

# Classical ψ formulas:
#   φ_m = X*C^2 - D*B
#   ψ_{2m}^2 * Q = C^2*(E*B^2 - A*D^2)^2
#   ψ_{2m+1} = E*C^3 - B*D^3
#   ψ_{2m-1} = D*B^3 - A*C^3
# Work with the Q-multiplied form to avoid division by ψ₂.

S = E*B^2 - A*D^2
Phi_m = X*C^2 - D*B
Psi_m_sq = C^2
Psi2m_sq_Q = C^2*S^2
Phi2m_Q = X*Psi2m_sq_Q - Q*(E*C^3 - B*D^3)*(D*B^3 - A*C^3)

res = Phi2m_Q * dupDen(Phi_m, Psi_m_sq) - Psi2m_sq_Q * dupNum(Phi_m, Psi_m_sq)

rels = [
    A*E - Q*B*D + T*C^2,      # ψ adjacent: AE = QBD - T C^2
    Q - Qpoly,
    T - Tpoly,
    4*b8 - b2*b6 + b4^2,
]
I = ideal(rels)
assert I.reduce(res) == 0
print([f.factor() for f in I.lift(res)])
```

Note the sign in the Somos relation:

```text
AE = QBD - T C^2
```

because

```lean
mk(ψ(m+2))*mk(ψ(m-2))
  = mk(C Ψ₂Sq)*mk(ψ(m+1))*mk(ψ(m-1)) - mk(C Ψ₃)*mk(ψ m)^2.
```

---

## Raw theorem by descent

Once `mk_dup_doubling_cross` is closed, the raw theorem is immediate.

```lean
namespace FLT.DivisionPolynomialDoubling

open Polynomial WeierstrassCurve
open WeierstrassCurve.Affine.CoordinateRing

variable {R : Type*} [CommRing R]
variable (W : WeierstrassCurve R)

theorem dup_doubling_cross (m : ℤ) :
    W.Φ (2 * m) * dupDenP W (W.Φ m) (W.ΨSq m)
      = W.ΨSq (2 * m) * dupNumP W (W.Φ m) (W.ΨSq m) := by
  let lhs : R[X] := W.Φ (2 * m) * dupDenP W (W.Φ m) (W.ΨSq m)
  let rhs : R[X] := W.ΨSq (2 * m) * dupNumP W (W.Φ m) (W.ΨSq m)
  have hmk : mk W.toAffine (Polynomial.C (lhs - rhs)) = 0 := by
    simpa [lhs, rhs, dupCrossDiff, map_sub] using mk_dup_doubling_cross (W := W) m
  have hpoly : lhs - rhs = 0 :=
    mk_C_eq_zero W.toAffine hmk
  exact sub_eq_zero.mp hpoly

end FLT.DivisionPolynomialDoubling
```

---

## Bottom line

The strategy in the prompt is the right one.  The only caveat is that I could not fetch the scratch files through the connector, so I cannot give a truly build-checked final line against the local normal form.

The most likely-to-build closing tactic for the coordinate-ring residual is:

```lean
polyrith
```

after rewriting by `mk_ψ`, `mk_Ψ_sq`, `mk_φ`, `mk_ψ₂_sq`, and `mk_psi_adjacent_somos`.  If `polyrith` does not close, use the Sage script above to generate the explicit `linear_combination` certificate.
