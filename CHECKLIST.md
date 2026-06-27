# FLT Formalization Checklist — Mazur |T|≤16 + QuarticD

## 主要目标（Milestone）
✅ Phase 1: Compile green (8761 jobs) + Axioms infrastructure (+569L Weil pairing tools)
🟡 Phase 2: QuarticD integration (d=2-7 analysis + Axiom 4 assembly)
⬜ Phase 3: Axiom 1 discharge (Weil pairing scaffold) / Axiom 2 fallback (two-invariant-factors)

---

## 原子列表 (Atoms) — 按优先级

### 🟡 ACTIVE: QuarticD + Axiom 4 Integration
- [ ] **A1**: QuarticD d↔n 映射验证（Q1 ChatGPT dm1 answered）
  - 输入：Kubert 参数化如何 reduce 到 quartic
  - 输出：d=2,3,4,5,6,7 → n=10,12,14,16 对应
  - 状态：答案在 commit c6ace8fc5@scratch（git-drop），等爸爸关键信息或浏览器粘贴

- [ ] **A2**: QuarticObstruction.lean 完成集成
  - 依赖：A1 (d↔n 映射)
  - 内容：3 主要定理 stub + case-split 组装
  - 状态：框架就位，待 A1 信息补全

- [ ] **A3**: QuarticD import + compile verify
  - 依赖：A1, A2
  - 任务：全库编译测试（scratch.QuarticD* → FLT/Assumptions）
  - 状态：框架编译待 A1-2 完成

### 🚀 IN DISPATCH: Axiom 1 (Weil Pairing)
- [ ] **B1**: Axiom 1 理论调研（Q2 ChatGPT dm2 answered）
  - 输入：Mathlib Weil pairing 状态 + 最小形式化路线
  - 输出：Codex 的 WeilPairing.lean 指导
  - 状态：答案被 bridge-capture 污染（DOM JS），等爸爸浏览器粘贴或 git-drop 恢复

- [ ] **B2**: WeilPairing.lean scaffold (Codex Pro 派遣中)
  - 依赖：B1 (理论指导)
  - 目标：compiled scaffold (0 sorry ideal, 2-5 named-sorry acceptable)
  - 状态：Codex 在制作（CODEX_AXIOM1_BRIEF.md）

- [ ] **B3**: Axiom 1 集成测试
  - 依赖：B2 (WeilPairing.lean)
  - 任务：wire 进 Axioms.lean + 全库编译
  - 状态：待 Codex 返回

### ⬜ FALLBACK: Axiom 2 (Two Invariant Factors)
- [ ] **C1**: TwoInvariantFactors.lean 实现（LOW-risk）
  - 依赖：Mathlib group theory (AddCommGroup.equiv_directSum_zmod_of_finite)
  - 难度：LOW (纯代数 + CRT，Mathlib 已有主要定理)
  - 启动条件：B2 遇到深层障碍（Weil pairing 需深 EC 理论）
  - 状态：框架就位（TwoInvariantFactors.lean），3 phases ready，待启动信号

---

## 工程检查 (Non-Atoms)

- [ ] **UNDERSTANDING.md 维护**：记录关键决策（当前缺少，应补）
- [ ] **CHECKLIST 及时更新**：每次 atom 动作后立即翻新此表
- [ ] **编译验证**：每个主要里程碑前 full `lake build`（当前：8761 jobs ✓）
- [ ] **axioms 清单**：`#print axioms FLT.Assumptions.MazurProof.Axioms` 显示当前 12 个 axioms 状态（todo：分类 discharged vs pending）

---

## 统筹进度 (Progress)

| 项目 | 状态 | 最后更新 |
|------|------|----------|
| 编译 | ✅ 8761 green | 2026-06-26 ~21:50 |
| Axioms.lean +569L | ✅ integrated | commit 4cc5d22 |
| QuarticD d=2-7 | ✅ proven (0 sorry) | prior commits |
| A1: d↔n mapping | ⏳ Q1 answered (git-drop) | ~22:00 |
| A2: QuarticObstruction | 🟡 framework ready | commit 823cfc5 |
| B1: Axiom 1 theory | ⏳ Q2 answered (DOM polluted) | ~22:00 |
| B2: WeilPairing.lean | 🚀 Codex Pro working | CODEX_AXIOM1_BRIEF.md |
| C1: TwoInvariantFactors | 🟡 3-phase scaffold ready | commit 153eef2 |
| CHECKLIST + UNDERSTANDING | ✅ unified docs | commits f31a93e + 050b4dd |

**Current blockers (low severity):**
1. A1: ChatGPT Q1 answered but in git-drop (需爸爸粘贴关键信息或我本地访问 scratch branch)
2. B1: ChatGPT Q2 污染（需爸爸浏览器粘贴 3-5 行 outline）
3. B2: Codex output (no ETA, likely overnight)

**Workaround: B 线自主推进**
- 倾向：不被 ChatGPT 格式卡住，继续推 C1 (Axiom 2)
- 可行：C1 三个 phase 完全独立，zero 对 A1/B1/B2 的依赖

**Gate to Phase 3:**
- A1 + A2 + A3 complete ✓ QuarticD integration done (needs Q1 key info, 预计 30 min)
- OR C1 完成（启动条件 = B2 stall，now advancing this path）
- Proceed to Axiom discharge once either path reaches critical

---

## Session Notes
- Started automode ~21:30
- Completed phases 1-2 of major push
- Dispatched 2 parallel ChatGPT questions (Q1, Q2)
- Recognized: ChatGPT dispatch discipline gap → fixed immediately
- Next: wait for ChatGPT + Codex, continue per "边跑边等" rule
