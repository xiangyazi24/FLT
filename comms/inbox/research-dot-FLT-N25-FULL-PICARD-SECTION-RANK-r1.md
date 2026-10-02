# Actual principal transport and the full Picard section-rank fibre formula

TASK_ID: FLT-N25-FULL-PICARD-SECTION-RANK
REVISION: 1
TYPE: RESULT
STATUS: ACTUAL-FULL-CLASS-FIBRE-INPUT-DISCHARGED
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 51bbb4f191ad0d3753b87123635c100a638ae580
DISPATCH_COMMIT: 9700ca106515f04411193844fbb347d40d86e481
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
DEPENDS_ON_RESULT: e862c484da703650baa98747a3123600a00c39d0
SUPERSEDES: none

N25F_SectionPrincipalTransport.lean proves that multiplication by the actual
function f satisfying div(f)=D-E is an F2-linear equivalence L(D) -> L(E).
It proves equality of dimensions for linearly equivalent full divisors, and
descends the actual section dimension to the full divisor-class quotient.
No arbitrary rank function or abstract linear-system premise is supplied.

N25F_FullPicardSectionRank.lean restricts this genuine rank to Pic^n and proves,
for every n and every actual degree-n class c, the exact existing-interface theorem

    Nat.card {E : fullClosedPointGrading25Two.EffDivOfDegree n //
      fullClosedPointGrading25Two.effectiveClass actualPrincipal
        actualPrincipal_degree_kernel n E = c}
      = CurveZetaClassNumber.linearSystemCard 2 (fullPicardSectionRank25Two n c).

The proof chooses a representative only to construct an exact equivalence
of fibres. The rank itself is representative-independent. This supplies the
full-grading middle-degree count's complete-linear-system fibre formulas,
in particular at n=4 and n=2, without truncating principal divisors.

## Validation

PASS: family-02 (principal transport and class-rank descent), five audits,
exit 0, 8.431 seconds, peak child RSS 2,158,696 KiB. SHA-256:
4399ca33c29d74b1b3df95048a360ef304cd7b455dcaba51f9ef4698e8b9457e.

PASS: picard-02 (actual effectiveClass adapter and exact linearSystemCard
format), four audits, exit 0, 12.237 seconds, peak child RSS 2,139,896 KiB.
SHA-256: fe26d26d9bbd1c5880e76e131d33639135010bf8496d2c80ad2a70f3ae908983.
All nine final audits are exactly [propext, Classical.choice, Quot.sound],
with no warnings or sorryAx. Portable generators reproduce the checked bytes.

The composed fixture contains the genuine section carrier, its full-degree
finiteness proof, principal multiplication maps, actual quotient class
construction, class degree and the effectiveClass definition. Previously
proved principal-map/order/degree/injectivity facts remain explicit proof
parameters only in the family; production closes each with its exact name.
The linearSystemCard definition was read at r34 blob
9cdd1f0b2ace516072ff96335c54f96231d49df3 and included verbatim.

FAIL: family-01 had a generator declaration-binding error, with rejected
sorryAx only downstream of that failure; source and logs are isolated under
failed/. The three-declaration picard-01 checkpoint passed with one unused-
parameter linter warning and is superseded by the clean final four-declaration
picard-02 check; its receipt is retained under prior/.

NOT RUN: full named FLT imports and their nine production audits. This packet
and earlier pending dependencies still require the lead's integration gate.
No fresh root axiom closure is inferred. Lean 4.31.0-rc2 compiler
5e44d5f905127c78a2da7a015fe7a47840c95eb1; Mathlib
96fd0fff3b8837985ae21dd02e712cb5df72ec05. Shared gate per check, one CPU/thread,
3072 MiB per Lean process, 60 active seconds. No broad build.

## Remaining geometry and next owned proof

The true section spaces, finiteness, exact class fibres and their genuine
ranks are now constructed in the candidate chain. Picard finiteness and the
genus-four identity rank(c)=rank(K-c)+1 are still unproved. The canonical
class must come from the actual differential/adjunction geometry.

The next owned step uses the genuine X-local DVR and its binary residue map
to prove the one-step filtration bound between L(D-X) and L(D), then the
upper bound dim L(D)<=max(deg D+1,0). This does not supply Riemann--Roch's
lower bound or prove Picard finiteness. N25/Mazur and all three root custom
axiom declarations remain open pending their own proofs and fresh audits.

Manifest: comms/inbox/research-dot-FLT-N25-FULL-PICARD-SECTION-RANK-r1-manifest.json
