# Session Handoff — 2026-07-10 (FLT Mazur proof)

automode: yes

## Branch synchronization

- Local `/Users/huangx/repos/flt`, GitHub `xiang/ai-scratch`, and UISAI2
  `/home/xhuan5/repos/flt-ai` synchronized and built the code state at
  `39b90f1d`; subsequent commits only update this handoff record.
- UISAI2 had three untracked files colliding with the fast-forward.  They are
  preserved in `stash@{0}` with message
  `pre-sync collision backup 2026-07-10`.
- The server has many other pre-existing untracked files; they were not
  modified or removed.

## Order 11 progress

The order-11 exclusion now has one `sorry`, reduced from two.  Everything from
an exact order-11 point through the explicit modular curve is checked Lean.

### Completed, zero `sorry`

1. `TateNormalFormBridge.lean`
   - Explicitly moves any marked point of order greater than three to `(0,0)`
     on Tate normal form.
   - Preserves additive order and proves the Tate parameter `b` is nonzero.
2. `TateOrder11.lean`
   - Proves `ψ₁₁(0,0) = b⁴⁰ F₁₁(b,c)` from Mathlib's division-polynomial
     recursion.
   - Proves both directions between `F₁₁(b,c)=0` and exact order 11 at the
     Tate origin, under nonsingularity and `b≠0`.
3. `RationalPointsN11.lean`
   - Proves that a nondegenerate rational solution of `F₁₁=0` gives a rational
     point on
     `Y² = X³ + 8X² + 16X + 16`
     with `X∉{0,-4}`.
4. `RationalPointsN11Descent.lean`
   - Proves the change of variables to
     `η² = ξ³ - 432ξ + 8208`.
   - Proves square-denominator normalization and the primitive integral model.
   - Checks the Lutz--Nagell exceptional-point finite enumeration: the only
     integral abscissas satisfying the discriminant condition are `-12,24`.
   - Proves the Billing--Mahler coefficient equations imply `x,a` even and
     `z` odd, then derives the impossible congruence `c² ≡ 2 (mod 4)`.
5. `BillingMahlerField.lean`
   - Constructs the cubic field using `alpha^3-4alpha^2+4alpha-2=0` and proves
     that `1,alpha,alpha^2` is the full integral basis.
   - Proves field discriminant `-44`, signature `(1,1)`, class number one, and
     unit rank one.
   - Proves `epsilon=alpha-1` and `-epsilon` are nonsquares, then derives the
     four unit squareclasses `1,-1,epsilon,-epsilon` from Dirichlet's theorem.
   - Proves the Mordell norm identity, principal-ideal-square extraction,
     positive-norm squareclass selection, integral coordinate extraction, and
     the three coefficient equations used by the parity contradiction.
6. `CyclicExclusion11.lean`
   - Replaces the abstract polynomial system by the concrete canonical system
     `[F₁₁]`, inequation `[b]`.
   - Closes the Tate-normal-form bridge and all downstream wiring.

### Exact remaining boundary

```lean
theorem billing_mahler_global_descent
    {ξ η : ℚ} (hcurve : MordellEquation ξ η)
    (x z y : ℤ) (hz : 0 < z) (hcop : Int.gcd x z = 1)
    (hξ : ξ = x / z^2)
    (hmodel : y^2 = x^3 - 432*x*z^4 + 8208*z^6) :
    (∃ x₀ y₀ : ℤ, ξ = x₀ ∧ η = y₀ ∧
      (y₀^2 = 0 ∨ y₀^2 ∣ 1496537856)) ∨
    ∃ I : Ideal (𝓞 K),
      y ≠ 0 ∧ span {descentInteger x z} = I^2 ∧
      ¬ IsSquare (descentElement x z)
```

This is the only remaining `sorry` in `CyclicExclusion11.lean`.  The ordinary
branch is now only the ideal-theoretic assertion that the primitive cubic
factor generates an ideal square and is not itself a field square.  Class
number one, unit-squareclass extraction, positivity, the coefficient
expansion, and the parity contradiction are all downstream Lean theorems.
The exceptional branch remains the fixed-curve Lutz--Nagell alternative.
Primary source:
G. Billing and K. Mahler, *On Exceptional Points on Cubic Curves*, JLMS 15
(1940), pp. 41--43: <https://carmamaths.org/resources/mahler/docs/067.pdf>.

## Correction to the previous handoff

The 2026-07-08 handoff incorrectly called the proposed 11a3 2-descent
certificate complete.  The original Q4012/Q4013 drop files show otherwise:

- Q4012 did not supply the promised local-obstruction table.
- Q4013 corrected the candidate set from a norm-one group to the norm-two
  coset `{-β,-βη,-βπ,-βηπ}` and observed that the `η` coefficient equations
  alone are soluble; the scalar/norm compatibility was still missing.

Do not reuse that certificate as a proof.

## Verification

On UISAI2:

```text
lake build FLT.Assumptions.MazurProof.CyclicExclusion11
Build completed successfully (8586 jobs).
```

The order-11 files contain exactly one `sorry`, at the global dichotomy above.
The whole `FLT/Assumptions/MazurProof` directory now has 11 theorem `sorry`s.
`#print axioms` shows only `propext`, `Classical.choice`, and `Quot.sound` for
every newly proved theorem; only the final order-11 theorem sees `sorryAx` via
the named global dichotomy.

## Next action

Formalize `billing_mahler_global_descent`: prove conjugate-ideal coprimality for
the primitive cubic factor (with the ramified-prime exceptional cases made
explicit), deduce that its principal ideal is a square, and prove the factor
is not a field square in the ordinary case.  Separately prove the fixed-curve
Lutz--Nagell alternative.  Do not replace this with a rank-zero axiom or the
incomplete Q4012/Q4013 certificate.
