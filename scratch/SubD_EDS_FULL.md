# sub-D NON-CIRCULAR coprimality — COMPLETE design (Xiang-pasted full dm2 EDS, authoritative)

Goal: preΨ'_root_not_Ψ₂Sq_root: preΨ'_n(x)=0 ⟹ Ψ₂Sq(x)≠0, NON-CIRCULAR (no point realization, no
2•P=0⟺Ψ₂Sq(x)=0). Route: evaluate the EDS preΨ'_n at a Ψ₂Sq root → the EDS param Ψ₂Sq² becomes 0 →
the specialized EDS = n·unit ≠ 0.

## SMALLEST non-circular KERNEL (pure EDS, NO elliptic curves — start here):
theorem preNormEDS'_zero_param_ne_zero {k}[Field k]{c d : k}{n}
  (hc : c ≠ 0)(hd : d² = -4*c³)(hn : (n:k)≠0) : preNormEDS' (0:k) c d n ≠ 0
Proof via 3 CLOSED FORMS (induction from preNormEDS'_zero/one/two/three/four + even/odd):
  preNormEDS' 0 c d (2s+1)   = (-1)^(s(s-1)/2) · c^(s(s+1)/2)
  preNormEDS' 0 c d (4s+2)   = (2s+1 : k) · c^(2s(s+1))
  preNormEDS' 0 c d (4(s+1)) = (s+1 : k) · c^(2s(s+2)) · d
All ≠0 when (n:k)≠0: odd→ ±c^k; 4s+2→ coeff (2s+1)=(n/2)≠0; 4(s+1)→ coeff (s+1)=(n/4)≠0 AND d≠0
(from d²=-4c³, c≠0, 2≠0).

## SUPPORT lemmas (elliptic-curve side, ring_nf identities):
1. eval_preΨ'_eq_preNormEDS'_eval (n)(x): (W.preΨ' n).eval x = preNormEDS' ((Ψ₂Sq.eval x)²)(Ψ₃.eval x)(preΨ₄.eval x) n
   — pure recursion lemma (induction from preNormEDS'_even/odd). preΨ' n IS preNormEDS' (Ψ₂Sq²) Ψ₃ preΨ₄ n.
2. preΨ₄_eval_sq_eq_neg_four_Ψ₃_eval_cube_of_Ψ₂Sq_eval_eq_zero (hx: Ψ₂Sq.eval x=0): (preΨ₄.eval x)²=-4(Ψ₃.eval x)³
   — via Ψ₂Sq ∣ preΨ₄²+4Ψ₃³ (expand + W.b_relation), eval at x, use hx.
3. Ψ₃_eval_ne_zero_of_Ψ₂Sq_eval_eq_zero (hx): Ψ₃.eval x ≠ 0 — Ψ₂Sq ⊥ Ψ₃ (no common 2-torsion singular root),
   via Ψ₂Sq_eq + twoTorsionPolynomial_discr + isUnit_Δ (elliptic).

## ASSEMBLY (short, non-circular):
preΨ'_eval_ne_zero_of_Ψ₂Sq_eval_eq_zero: rw eval_preΨ' + hx → preNormEDS' 0 c d n; apply kernel with hc(support3),hd(support2).
preΨ'_root_not_Ψ₂Sq_root := contrapose.

## VERDICT: CLOSEABLE. The kernel preNormEDS'_zero_param_ne_zero is the smallest honest grind (pure EDS,
3 closed forms by induction). Resultant route is STRICTLY MORE infra (needs the same eval formula + root-product
bookkeeping). Named API: preNormEDS'_zero/one/two/three/four/even/odd, preΨ'_even/odd, Ψ₂Sq_eq, twoTorsionPolynomial_discr.
