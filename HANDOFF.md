# Handoff: Mazur |T|≤16 Formalization

## Where we are
- **Repo**: uisai2:~/repos/flt-ai, branch `ai-scratch`
- **Fork**: github.com/xiangyazi24/FLT (ChatGPT git-drop target)
- **Status**: 0 sorry, 12 axioms, ~4000 LOC

## What's running RIGHT NOW
1. **Codex PID 171018** on uisai2: writing `scratch/DescentAssembly.lean` — the full chain to discharge `obstruction_curve_20a4_points_degenerate`. Check: `cat /tmp/codex_assembly_output.log | tail -30`
2. **ChatGPT dm1/dm2**: idle, available for git-drop tasks

## The critical path to FIRST AXIOM DISCHARGE

ChatGPT (dm2) gave us the concrete architecture (saved at `scratch/strategy_descent_concrete.md` on the fork). The chain:

```
rational point P=(x,y) on y²=x³+x²-x, x≠0
    ↓ write x = d·u² (squareclass decomposition)
    ↓ descent_map (PROVED, scratch/DescentMap.lean)
cover C_d has a rational point
    ↓ bad-prime argument: if prime p∤10 and p|d, C_d has no p-adic point
    ↓ so d divides 10 up to squares: d ∈ {±1,±2,±5,±10}
    ↓ Selmer obstructions (PROVED, 12 files): d∈{±2,±5,±10} → C_d trivial
d ∈ {1,-1}, so x = ±(rational)²
    ↓ integer descent (PROVED, scratch/Descent20a4.lean)
x ∈ {-1, 0, 1}
```

**What's done** (all 0 sorry):
- DescentMap.lean: step 1 (descent map)
- Selmer*.lean (12 files): step 3 (local obstructions)  
- Descent20a4.lean: step 4 (integer case)

**What's NOT done**:
- Squareclass decomposition: x ∈ Q* → x = d·u² for squarefree d
- Bad-prime argument: p∤10, p|d → C_d has no p-adic point (same descent pattern as Selmer files)
- Assembly connecting all pieces

## ChatGPT git-drop workflow

Skills in `~/repos/zinan-skills/` (symlinked to `~/.claude/skills/`).

```bash
# Send task (task in the question, NOT in the drop file):
python3 -u ~/.openclaw/workspace/scripts/ask-gpt.py dm1 <<'EOQ'
<question>
Write COMPLETE response into scratch/_CHATGPT_DROP_dm1.md on ai-scratch (UPDATE). Report SHA.
EOQ

# Harvest:
git fetch xiang ai-scratch
git show xiang/ai-scratch:scratch/_CHATGPT_DROP_dm1.md > /tmp/answer.md
# Extract lean:
awk '/^```lean$/{f=1;next} f&&/^```$/{exit} f{print}' /tmp/answer.md > /tmp/answer.lean
# Compile:
cd ~/repos/flt-ai && PATH=$HOME/.elan/bin:$PATH lake env lean /tmp/answer.lean
```

Drop files: `scratch/_CHATGPT_DROP_dm1.md`, `scratch/_CHATGPT_DROP_dm2.md`

## CHECKLIST

File: `uisai2:~/repos/flt-ai/MAZUR_CHECKLIST.md`

## Key files inventory

| File | What | Status |
|------|------|--------|
| FLT/Assumptions/MazurProof/Axioms.lean | 12 axioms | target |
| FLT/Assumptions/MazurProof/TorsionBound.lean | main theorem | 0 sorry |
| scratch/DescentMap.lean | descent map | 0 sorry |
| scratch/Descent20a4.lean | integer case N=10 | 0 sorry |
| scratch/Selmer20a4.lean + 11 others | 12 Selmer obstructions | 0 sorry |
| scratch/QuarticD{2..10}.lean | d-by-d quartics | 0 sorry (dead end for uniform) |
| scratch/TwoTorsionBound.lean | |E[2]|≤4 | 0 sorry (by Codex) |
| scratch/InvariantFactorLemmas.lean | group theory | 0 sorry |

## Build

```bash
cd ~/repos/flt-ai
export PATH=$HOME/.elan/bin:$PATH
lake env lean scratch/<file>.lean        # single file
lake build FLT.Assumptions.MazurProof.TorsionBound  # full chain
```

## Axiom check

```bash
echo 'import FLT.Assumptions.MazurProof.TorsionBound
open MazurProof in #print axioms mazur_torsion_bound' | lake env lean --stdin
```
