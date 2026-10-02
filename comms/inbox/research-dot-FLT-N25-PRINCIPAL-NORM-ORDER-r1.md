# Local factor lengths and principal norm order

TASK_ID: FLT-N25-PRINCIPAL-NORM-ORDER
REVISION: 1
TYPE: RESULT
STATUS: BOUNDED-PRINCIPAL-FUNCTION-STEP-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 51bbb4f191ad0d3753b87123635c100a638ae580
DISPATCH_COMMIT: 9700ca106515f04411193844fbb347d40d86e481
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
DEPENDS_ON_RESULT: 6a4110a03ca7bee2db5fb2e506eb75edd3643ce0
SUPERSEDES: none; next bounded principal-function step under r34

## Exact dependency and candidates

R34 remains the latest verified acceptance. The preceding arbitrary-ideal
norm-multiplicity candidate was published at the full dependency commit above;
all 15 files and branch were read back exactly. Its production acceptance
is still pending. This packet builds on that candidate without relabeling it
as accepted.

comms/candidates/N25F_LocalFactorOrder.lean contains two genuine generic
Dedekind-domain theorems:

    local_length_eq_factor_count (I : Ideal R) (hI : I ≠ ⊥)
        (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥) :
      Module.length (Localization.AtPrime p)
        ((Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))) =
      (normalizedFactors I).count p

    ord_algebraMap_eq_factor_count (a : R) (ha : a ≠ 0)
        (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥) :
      Ring.ord (Localization.AtPrime p) (algebraMap R (Localization.AtPrime p) a) =
      (normalizedFactors (Ideal.span {a})).count p

They factor I as the exact power of p times a coprime ideal, localize the
coprime factor to the unit ideal, and apply the DVR quotient-length theorem.
The principal case unfolds the actual length definition of Ring.ord.

comms/candidates/N25F_InfinityPrincipalNormOrder.lean has one public theorem,
infinity_intNorm_local_order. For every nonzero a in the actual reciprocal
normalization it proves

    ord_(T)(intNorm(a)) = ord_X(a) + ord_YZ(a) + ord_Z(a).

Each ord is literally Ring.ord in the localization at the named actual prime,
applied to its canonical algebraMap. The candidate states all maps explicitly.
It applies the preceding ideal-multiplicity theorem to span {a}, rewrites
Ideal.relNorm_singleton, and uses the two length theorems. Nonvanishing of the
integral norm follows from the already available relative-ideal norm theorem;
no separate norm or order compatibility assumption is added.

## Check ledger

PASS: LocalFactorOrderCheck.lean is the exact full production source followed
only by two print-axioms commands. production-02: exit 0, 4.075 seconds,
peak child RSS 2,752,656 KiB. Both axioms exactly the standard three.
Its production SHA-256 is
767d4266bf8021c409fce2467b28fcebd78739d01917f5f1b9d1c8d5f4a4f07f.
The first check failed because rw also rewrote the factor count on the RHS;
the correction restricts the factorization rewrite to the LHS. No theorem
statement changed. The final check is warning-free and has no sorryAx.

PASS: PrincipalNormOrderFamilyCheck.lean, principal-01: exit 0, 4.618 seconds,
peak child RSS 2,899,596 KiB. All three audits are standard-three and clean.
It includes the unchanged exact local-factor source and transparently
generalizes only the actual rings, primes, their nonvanishing proofs and the
preceding proven ideal-multiplicity statement. The attached generator shows
each substitution. The production specialization supplies the named facts.
Its source SHA-256 is
fac5eccca0152624c0f6c5da3a01943695f278a6abedcdd34be127e202acf9d7.

NOT RUN locally: full named FLT imports and three production declarations
in the integrated environment. ActualPrincipalNormOrderCheck.lean enumerates
that gate for the lead. The generic-family test is not a full FLT test.

Pins: Lean 4.31.0-rc2 / 5e44d5f905127c78a2da7a015fe7a47840c95eb1;
Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05. One CPU/thread,
3,072 MiB Lean cap, 60 active seconds and one shared lock per check.
No broad build, duplicate validation run or accepted-source change occurred.

## Remaining boundary

This completes the bounded regular-normalization-element step. Transport to
the already identified boundary local rings, extension to fractions, conversion
to the actual fixed-field norm and comparison with the affine norm-degree
identity remain subsequent steps. The general projective product formula,
N25 and Mazur remain open. The last fresh root closure still has no sorryAx
and exactly the same three custom axioms.

Manifest: comms/inbox/research-dot-FLT-N25-PRINCIPAL-NORM-ORDER-r1-manifest.json
