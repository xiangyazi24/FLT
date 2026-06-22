# Q298-dm1: Ward/Stange — exact published induction and what is *not* in Stange

## Bottom line

There is **no** Stange thesis lemma/theorem that proves the four-term elliptic-net recurrence from adjacent Somos by a well-founded induction on recurrence instances.

In Stange, the four-term relation is the **definition** of an elliptic net:

```text
EN(p,q,r,s):
W(p+q+s) W(p-q) W(r+s) W(r)
+ W(q+r+s) W(q-r) W(p+s) W(p)
+ W(r+p+s) W(r-p) W(q+s) W(q) = 0.
```

Chapter 4 of the thesis is a baseset/Laurentness induction **assuming** all instances of this recurrence are available. It is not a proof that `EN(p,q,r,s)` follows from smaller `EN` instances or from the adjacent Somos relation.

The exact published induction relevant to your goal is instead:

```text
Alf van der Poorten and Christine S. Swart,
"Recurrence Relations for Elliptic Sequences: Every Somos 4 is a Somos k",
Section 6, Theorem 3, equations (13), (14), and the displayed identities (15) and the following product identity.
```

This induction proves the all-gap Ward formula and its off-by-one companion. It is **not** a `linear_combination` of lower Stange instances; it is a simultaneous multiplicative gap induction using quotient identities. For Lean, the quotient proof can be run over the universal fraction field/domain and then denominators cleared / transported.

---

## Stange: the actual induction measure in Chapter 4

Stange's Chapter 4 defines an implication system for computing terms from recurrence relations. The recurrence instances are encoded by

```text
F(p,q,r,s) =
[ p+q+s, p-q, r+s, r
| q+r+s, q-r, p+s, p
| r+p+s, r-p, q+s, q ].
```

The measure sometimes used to order those baseset inductions is

```text
N(v) := max_i |v_i|.
```

But this is a measure on **terms** `W(v)`, not on recurrence quadruples `(p,q,r,s)`, and the induction proves that terms are generated from a baseset. It does not give an induction proving a target recurrence instance from lower recurrence instances.

Concrete Stange anchors:

```text
Thesis Definition 4.1.1: implication / S-integral implication.
Thesis Definition 4.1.2: N(v) = max_i |v_i|.
Thesis Theorem 4.2.1: rank-one generation, cited to Ward [Thm 4.1].
Thesis Theorem 4.4.1: Laurentness / finite baseset generation.
```

For the actual recurrence of net polynomials, the source is analytic/Zariski, not inductive:

```text
Paper Theorem 3.7: complex Ω_v form an elliptic net, proved by sigma-function identities.
Paper Theorem 4.1: arbitrary-field net polynomials inherit the elliptic-net recurrence by uniqueness/Zariski density.
```

So the requested object

```text
target EN(p,q,r,s)
  = finite linear_combination of smaller EN(p',q',r',s') plus adjacent Somos
```

is not a published Stange lemma and I would not build against it.

---

## The exact published Ward/Somos induction to use

Work in a field for the displayed quotient algebra; in a formal proof over a domain, clear denominators. Let `(A_h)` and `(W_h)` be two antisymmetric two-sided sequences. Define `e_h` and `\bar e_h` by

```text
A_{h-1} A_{h+1} = e_h A_h^2,
W_{h-1} W_{h+1} = \bar e_h W_h^2.
```

Assume both `e` and `\bar e` satisfy the same elliptic/Somos-4 invariants

```text
(E4)  e_{t-1} e_t^2 e_{t+1} = α^2 e_t − β,
(E5)  (e_{t-1} + e_{t+1}) e_t^2 = γ e_t − α^2,
```

and the same identities with `e` replaced by `\bar e`.

Van der Poorten--Swart Theorem 3 proves, for all integers `m`,

```text
(13)  W_1^2 A_{h-m} A_{h+m}
    = W_m^2 A_{h-1} A_{h+1}
      − W_{m-1} W_{m+1} A_h^2,
```

and

```text
(14)  W_1 W_2 A_{h-m} A_{h+m+1}
    = W_m W_{m+1} A_{h-1} A_{h+2}
      − W_{m-1} W_{m+2} A_h A_{h+1}.
```

For your normalized rank-one target, set `A = W` and `W_1 = 1`. Then `(13)` is exactly

```text
AddRel(h,m):
W(h+m) W(h-m)
= W(m)^2 W(h+1) W(h-1)
  − W(m+1) W(m-1) W(h)^2.
```

And `(14)` is exactly the off-by-one companion

```text
OffRel(m,h):
W(2) W(h+m+1) W(h-m)
= W(h+2) W(h-1) W(m+1) W(m)
  − W(m+2) W(m-1) W(h+1) W(h).
```

---

## Well-founded measure

Use simultaneous induction on the nonnegative gap `m`.

Practical base set for a division-free formalization:

```text
P_0(h), P_1(h)    trivial/antisymmetry/unit cases,
P_2(h)            adjacent Somos = AddRel(h,2),
Q_0(h), Q_1(h)    trivial/antisymmetry/unit cases,
Q_2(h)            the gap-5/off companion at m=2.
```

The published proof states the result for `m ∈ ℤ`; negative gaps are handled by antisymmetry. For formalization, prove `m ≥ 0` and derive the negative cases separately.

---

## Exact induction algebra: the gap/AddRel step

Define the normalized ratio

```text
R_m(h) := A_{h-m} A_{h+m} / A_h^2.
```

The theorem `(13)` says

```text
R_m(h) = (W_m^2 / W_1^2) · (e_h − \bar e_m).
```

To prove the target `P_{m+1}(h)`, use exactly these lower instances:

```text
P_m(h−1)   = AddRel(h−1,m) = Stange(h−1,m,1,0),
P_m(h+1)   = AddRel(h+1,m) = Stange(h+1,m,1,0),
P_{m−1}(h) = AddRel(h,m−1) = Stange(h,m−1,1,0).
```

The regrouping tautology is

```text
R_{m+1}(h)
= R_m(h−1) · e_h^2 · R_m(h+1) / R_{m−1}(h).
```

Expanded only as indices, this is

```text
A_{h-m-1} A_{h+m+1} / A_h^2
=
  (A_{h-1-m} A_{h-1+m} / A_{h-1}^2)
  · (A_{h-1} A_{h+1} / A_h^2)^2
  · (A_{h+1-m} A_{h+1+m} / A_{h+1}^2)
  /
  (A_{h-(m-1)} A_{h+(m-1)} / A_h^2).
```

After substituting the three lower `P` instances, this becomes

```text
R_{m+1}(h)
=
(W_m^4 / (W_{m-1}^2 W_1^2))
· ((e_{h-1} − \bar e_m) e_h^2 (e_{h+1} − \bar e_m))
  / (e_h − \bar e_{m-1}).
```

Since

```text
\bar e_m = W_{m-1} W_{m+1} / W_m^2,
```

this is the desired

```text
R_{m+1}(h) = (W_{m+1}^2 / W_1^2) · (e_h − \bar e_{m+1})
```

if and only if

```text
(15)
(e_{h-1} − \bar e_m) e_h^2 (e_{h+1} − \bar e_m)
=
(\bar e_{m-1} − e_h) \bar e_m^2 (\bar e_{m+1} − e_h).
```

This is the literal closing identity in the published proof. It is checked from `(E4)` and `(E5)` by expanding the left side:

```text
(e_{h-1} − \bar e_m) e_h^2 (e_{h+1} − \bar e_m)
= e_{h-1} e_h^2 e_{h+1}
  − \bar e_m (e_{h-1}+e_{h+1}) e_h^2
  + \bar e_m^2 e_h^2
= α^2 e_h − β
  − (γ \bar e_m e_h − α^2 \bar e_m)
  + \bar e_m^2 e_h^2,
```

which is symmetric under `e_h ↔ \bar e_m`.

---

## Exact induction algebra: the off-by-one companion step

Define

```text
U_m(h) := A_{h-m} A_{h+m+1} / (A_h A_{h+1}),
V_m(h) := (W_1 W_2 / (W_m W_{m+1})) · U_m(h).
```

The theorem `(14)` says

```text
V_m(h) = e_h e_{h+1} − \bar e_m \bar e_{m+1}.
```

To prove the target `Q_{m+1}(h)`, use exactly these lower instances:

```text
Q_m(h−1)   = OffRel(m,h−1) = Stange(h−1,m,1,1),
Q_m(h+1)   = OffRel(m,h+1) = Stange(h+1,m,1,1),
Q_{m−1}(h) = OffRel(m−1,h) = Stange(h,m−1,1,1).
```

The regrouping tautology is

```text
U_{m+1}(h)
= U_m(h−1) · (e_h e_{h+1}) · U_m(h+1) / U_{m−1}(h).
```

Equivalently, in the normalized `V` variables,

```text
V_{m+1}(h)
=
  V_m(h−1) · e_h e_{h+1} · V_m(h+1)
  /
  (\bar e_m \bar e_{m+1} · V_{m−1}(h)).
```

After substituting the three lower `Q` instances, this becomes

```text
V_{m+1}(h)
=
((e_{h-1} e_h − \bar e_m \bar e_{m+1})
 · e_h e_{h+1}
 · (e_{h+1} e_{h+2} − \bar e_m \bar e_{m+1}))
/
(\bar e_m \bar e_{m+1}
 · (e_h e_{h+1} − \bar e_{m-1} \bar e_m)).
```

This is the desired

```text
V_{m+1}(h) = e_h e_{h+1} − \bar e_{m+1} \bar e_{m+2}
```

if and only if

```text
(e_{h-1} e_h − \bar e_m \bar e_{m+1})
  e_h e_{h+1}
  (e_{h+1} e_{h+2} − \bar e_m \bar e_{m+1})
=
(\bar e_{m-1} \bar e_m − e_h e_{h+1})
  \bar e_m \bar e_{m+1}
  (\bar e_{m+1} \bar e_{m+2} − e_h e_{h+1}).
```

The published proof closes it by the symmetric expansion

```text
(e_{h-1}e_h − \bar e_m\bar e_{m+1}) e_h e_{h+1}
  (e_{h+1}e_{h+2} − \bar e_m\bar e_{m+1})
=
β e_h e_{h+1} + (α^4 − βγ)
− (α^2(e_h+e_{h+1}) − 2β) \bar e_m \bar e_{m+1}
+ e_h e_{h+1} \bar e_m^2 \bar e_{m+1}^2
```

and then replacing

```text
α^2(e_h+e_{h+1}) = e_h e_{h+1}(γ − e_h e_{h+1}) + β
```

makes the expression visibly symmetric under

```text
e_h e_{h+1} ↔ \bar e_m \bar e_{m+1}.
```

---

## Literal lower-instance list in Stange tuple notation

For the `AddRel` target

```text
Target: EN(h, m+1, 1, 0)
```

use

```text
EN(h−1, m,   1, 0),
EN(h+1, m,   1, 0),
EN(h,   m−1, 1, 0),
```

plus the `e`-symmetry identity `(15)`, which is a consequence of the adjacent Somos/e-invariants, not a lower `EN` instance.

For the off companion target

```text
Target: EN(h, m+1, 1, 1)
```

use

```text
EN(h−1, m,   1, 1),
EN(h+1, m,   1, 1),
EN(h,   m−1, 1, 1),
```

plus the product `e`-symmetry identity displayed above.

There is no published Stange `linear_combination` with W-cofactors that sums those lower `EN` instances to the target. The exact published step is the multiplicative quotient step above.

---

## Recommendation for the Lean build

Do **not** try to build a Stange-recursion induction over quadruples `(p,q,r,s)`. The source does not contain such an induction.

For `normEDS`, the most faithful formal route is:

1. Prove the adjacent Somos base `P_2(h) = AddRel(h,2)`.
2. Prove the companion base `Q_2(h) = OffRel(2,h)` or derive it from your odd/even normEDS recurrences.
3. Define the `e`-invariants in the universal fraction field/domain:

   ```text
   e_h := W(h−1) W(h+1) / W(h)^2.
   ```

4. Prove `(E4)` and `(E5)` for `e` from adjacent Somos.
5. Run the simultaneous induction above for `P_m` and `Q_m`.
6. Specialize `A = W`, `W_1 = 1`, and map the universal identity back to arbitrary `CommRing` targets.

This keeps combined indices throughout and avoids the false local cancellation step.
