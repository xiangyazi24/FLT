# Q869 (dm3): strengthening the induction hypothesis vs. a ranked pair induction

## Bottom line

Yes, there is a clean Lean setup, but I would phrase it slightly differently from ordinary lexicographic induction on `(n, flag)`.

The right idea is to make two kinds of proof obligations:

```lean
SepJob.psi n      -- rootwise separability of preΨ' n
SepJob.cof k      -- rootwise separability of the even cofactor in preΨ' (2*k)
```

and then put `SepJob.cof k` **immediately before** `SepJob.psi (2*k)` in the well-founded order.  This gives exactly the dependency you want:

```text
all SepJob.psi m with m < 2k     <   SepJob.cof k   <   SepJob.psi (2k).
```

So, while proving the cofactor at index `k`, you may use separability of the nearby polynomials `preΨ'(k-2)`, `preΨ'(k-1)`, `preΨ'(k+1)`, `preΨ'(k+2)`, because they are all `< 2k` once `k ≥ 3`.  Then, while proving `preΨ'(2k)`, you may use both `SepJob.psi k` and `SepJob.cof k`.

However, this only breaks the **even/cofactor** circularity.  It does **not** by itself break the earlier odd/even circularity if the odd proof still tries to prove `SepJob.psi n` by calling `SepJob.psi (2*n)`.  No well-founded order can simultaneously allow

```text
SepJob.psi n      < SepJob.psi (2*n)      -- needed by the even proof
SepJob.psi (2*n)  < SepJob.psi n          -- needed by odd-via-even
```

for nontrivial `n`.  So the pair/ranked induction is useful only if the odd case has a direct proof, or reduces to strictly lower jobs.  In practice, that means the odd case should come from the invariant-differential / quotient identity, or from a direct polynomial identity, not by invoking separability of `preΨ'(2n)`.

## Why the naive strengthened IH is almost right but awkward

If the induction theorem is

```text
P n := Sep(preΨ' n) ∧ CofSep(n),
```

where `CofSep(n)` means separability of the cofactor in

```text
preΨ'(2n) = preΨ'(n) * evenCof n,
```

then the even case for `preΨ'(2k)` can indeed use `P k`, since `k < 2k`.  Thus Case B is not circular at the level of the even proof.

The awkward part is proving `CofSep(k)` inside `P k`.  The cofactor formula at index `k` naturally mentions `preΨ'(k-2)`, `preΨ'(k-1)`, `preΨ'(k+1)`, and `preΨ'(k+2)`.  The terms `k+1` and `k+2` are not available from ordinary strong induction on `k`.  They are, however, smaller than `2k`, which is the ambient polynomial whose cofactor you are analyzing.

So the cofactor obligation should not live at level `k`.  It should live at level `2k`, just before the main separability theorem for `2k`.

## Recommended order

Use a single indexed family of goals and a numeric rank.

```lean
import Mathlib.Tactic

noncomputable section

namespace DivisionPolynomial

/-!
Replace `PsiSep` and `CofSep` by the actual predicates in the FLT files.

`PsiSep n` should mean rootwise separability of `preΨ' n`.
`CofSep k` should mean rootwise separability of the even cofactor `evenCof k`
appearing in `preΨ' (2*k) = preΨ' k * evenCof k`.
-/

variable {K : Type*} [Field K]

-- Placeholder names.  In the real file, use the existing definitions.
def PsiSep (_n : ℕ) : Prop := True
def CofSep (_k : ℕ) : Prop := True

inductive SepJob where
  | psi : ℕ → SepJob
  | cof : ℕ → SepJob
  deriving DecidableEq

namespace SepJob

/--
Rank the cofactor for `2*k` immediately before the main goal for `2*k`.

* `psi n` has rank `2*n + 1`.
* `cof k` has rank `4*k`, i.e. just before `psi (2*k)`, whose rank is `4*k + 1`.

Thus:

* `psi m < cof k` whenever `m < 2*k`;
* `cof k < psi (2*k)`;
* `cof j < cof k` whenever `j < k`.
-/
def rank : SepJob → ℕ
  | .psi n => 2 * n + 1
  | .cof k => 4 * k

end SepJob

/-- The proposition attached to each job. -/
def SepStmt : SepJob → Prop
  | .psi n => PsiSep (K := K) n
  | .cof k => CofSep (K := K) k

end DivisionPolynomial
```

This rank is usually easier than using `Prod.Lex` explicitly.  It is just the lexicographic order on the conceptual key

```text
psi n  ↦ (n, 1)
cof k  ↦ (2k, 0),
```

encoded as a natural number.

## The proof skeleton

The main theorem should be a well-founded induction over `SepJob.rank`.

```lean
import Mathlib.Tactic

noncomputable section

namespace DivisionPolynomial

variable {K : Type*} [Field K]

-- Real project predicates go here.
def PsiSep (_n : ℕ) : Prop := True
def CofSep (_k : ℕ) : Prop := True

inductive SepJob where
  | psi : ℕ → SepJob
  | cof : ℕ → SepJob
  deriving DecidableEq

namespace SepJob

def rank : SepJob → ℕ
  | .psi n => 2 * n + 1
  | .cof k => 4 * k

end SepJob

def SepStmt : SepJob → Prop
  | .psi n => PsiSep (K := K) n
  | .cof k => CofSep (K := K) k

/- Placeholder lemma interfaces.  These are the real mathematical atoms to prove. -/

/-- Small `preΨ' n` cases, such as `n = 0, 1, 2`, depending on your indexing convention. -/
axiom psiSep_small : ∀ n : ℕ, n ≤ 2 → PsiSep (K := K) n

/-- Small even-cofactor cases where `k+2 < 2*k` is false. -/
axiom cofSep_small : ∀ k : ℕ, k < 3 → CofSep (K := K) k

/--
Even product step:
`preΨ'(2*k) = preΨ'(k) * evenCof k`.
The proof uses rootwise separability of both factors plus the no-common-root lemma.
-/
axiom psiSep_even_of_sep_cof :
    ∀ k : ℕ, 0 < k →
      PsiSep (K := K) k →
      CofSep (K := K) k →
      PsiSep (K := K) (2 * k)

/--
Direct odd step.
Important: this must not call `PsiSep (2*n)`.  It may use only strictly lower jobs.
For example, this could be the invariant-differential / quotient-identity proof.
-/
axiom psiSep_odd_direct :
    ∀ k : ℕ,
      (∀ m : ℕ, m < 2 * k + 1 → PsiSep (K := K) m) →
      (∀ j : ℕ, 4 * j < 2 * (2 * k + 1) + 1 → CofSep (K := K) j) →
      PsiSep (K := K) (2 * k + 1)

/--
Cofactor step.
This is where the ranking matters.  For `3 ≤ k`, the proof may use
`PsiSep m` for every `m < 2*k`, including `k-2`, `k-1`, `k+1`, and `k+2`.
It may also use earlier cofactor goals.
-/
axiom cofSep_of_lower :
    ∀ k : ℕ, 3 ≤ k →
      (∀ m : ℕ, m < 2 * k → PsiSep (K := K) m) →
      (∀ j : ℕ, j < k → CofSep (K := K) j) →
      CofSep (K := K) k

/-- All jobs, proved in the ranked order. -/
theorem allSepJob : ∀ j : SepJob, SepStmt (K := K) j := by
  intro j
  refine (measure_wf SepJob.rank).induction ?step j
  intro j ih
  cases j with
  | psi n =>
      by_cases hsmall : n ≤ 2
      · exact psiSep_small n hsmall
      · -- Split `n` by parity.  Use whatever parity split is most convenient
        -- in the actual file.
        rcases Nat.even_or_odd n with hEven | hOdd
        · rcases hEven with ⟨k, hk⟩
          subst n
          have hkpos : 0 < k := by omega
          exact psiSep_even_of_sep_cof k hkpos
            (ih (.psi k) (by
              dsimp [SepJob.rank]
              omega))
            (ih (.cof k) (by
              dsimp [SepJob.rank]
              omega))
        · rcases hOdd with ⟨k, hk⟩
          subst n
          exact psiSep_odd_direct k
            (fun m hm =>
              ih (.psi m) (by
                dsimp [SepJob.rank]
                omega))
            (fun j hj =>
              ih (.cof j) (by
                dsimp [SepJob.rank]
                omega))
  | cof k =>
      by_cases hk : k < 3
      · exact cofSep_small k hk
      · have hk3 : 3 ≤ k := by omega
        exact cofSep_of_lower k hk3
          (fun m hm =>
            ih (.psi m) (by
              dsimp [SepJob.rank]
              omega))
          (fun j hj =>
            ih (.cof j) (by
              dsimp [SepJob.rank]
              omega))

/-- Main exported theorem. -/
theorem psiSep_all (n : ℕ) : PsiSep (K := K) n :=
  allSepJob (K := K) (.psi n)

/-- Cofactor exported theorem, if useful elsewhere. -/
theorem cofSep_all (k : ℕ) : CofSep (K := K) k :=
  allSepJob (K := K) (.cof k)

end DivisionPolynomial
```

The exact syntax of `Nat.even_or_odd` may need adjustment depending on the imports and the local shape you prefer.  The important part is the ranking; the `omega` obligations are exactly the arithmetic facts you want Lean to check.

## Why this order matches the cofactor formula

For the cofactor proof at index `k`, the hard calls look like this:

```lean
have h_km2 : PsiSep (K := K) (k - 2) :=
  ih (.psi (k - 2)) (by
    dsimp [SepJob.rank]
    omega)

have h_km1 : PsiSep (K := K) (k - 1) :=
  ih (.psi (k - 1)) (by
    dsimp [SepJob.rank]
    omega)

have h_kp1 : PsiSep (K := K) (k + 1) :=
  ih (.psi (k + 1)) (by
    dsimp [SepJob.rank]
    omega)

have h_kp2 : PsiSep (K := K) (k + 2) :=
  ih (.psi (k + 2)) (by
    dsimp [SepJob.rank]
    omega)
```

These are valid under `3 ≤ k` because

```text
k - 2 < 2k,
k - 1 < 2k,
k + 1 < 2k,
k + 2 < 2k.
```

In rank form, for example,

```text
rank (psi (k+2)) = 2*(k+2)+1 < 4*k = rank (cof k)
```

exactly when `3 ≤ k`.

Then, in the even product proof,

```lean
have hψk : PsiSep (K := K) k :=
  ih (.psi k) (by
    dsimp [SepJob.rank]
    omega)

have hcofk : CofSep (K := K) k :=
  ih (.cof k) (by
    dsimp [SepJob.rank]
    omega)
```

because

```text
rank (psi k) = 2k+1 < 4k+1 = rank (psi (2k)),
rank (cof k) = 4k   < 4k+1 = rank (psi (2k)).
```

That is precisely the intended dependency graph.

## What this does and does not prove

This setup is a good Lean implementation of the strengthened induction idea, but the mathematical work is still in two atoms.

First, you need a real lemma of the form

```lean
cofSep_of_lower :
  ∀ k, 3 ≤ k →
    (∀ m, m < 2*k → PsiSep m) →
    (∀ j, j < k → CofSep j) →
    CofSep k
```

This is where the cofactor formula involving `k-2`, `k-1`, `k+1`, `k+2` belongs.  The ranked induction gives you the right hypotheses for it.

Second, the odd case must be genuinely direct:

```lean
psiSep_odd_direct :
  ... → PsiSep (2*k+1)
```

It must not be implemented as

```lean
have h2n : PsiSep (2*(2*k+1)) := ...
```

because that recreates the old cycle.  The ranked induction will prevent that call: `rank (psi (2*n))` is larger than `rank (psi n)`.

So the clean Lean answer is:

1. Use a single `SepJob` family rather than two separate mutually recursive theorems.
2. Rank `cof k` immediately before `psi (2*k)`.
3. Prove the cofactor lemma from all `psi m` with `m < 2*k`.
4. Keep the odd case direct; do not reduce odd separability to even separability of `2n`.

## Practical recommendation

I would add the infrastructure in this order:

```lean
inductive SepJob where
  | psi : ℕ → SepJob
  | cof : ℕ → SepJob

namespace SepJob
  def rank : SepJob → ℕ
    | .psi n => 2*n + 1
    | .cof k => 4*k
end SepJob

def SepStmt : SepJob → Prop
  | .psi n => PsiSep n
  | .cof k => CofSep k
```

Then prove the following standalone lemmas before doing the well-founded induction:

```lean
psiSep_small
cofSep_small
psiSep_even_of_sep_cof
cofSep_of_lower
psiSep_odd_direct
```

Once those atoms exist, the final induction should be only wiring plus `omega`.

This is better than a standard `(n, flag)` lexicographic induction with `cof k` at level `k`, because the cofactor proof needs facts up to `k+2`.  The cofactor really belongs to the ambient level `2k`, not to the source level `k`.
