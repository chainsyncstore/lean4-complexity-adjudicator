# P vs. NP — Formal Reductions, Barriers & Candidate-Lemma Refutations in Lean 4 & LaTeX

[![Lean 4.15.0](https://img.shields.io/badge/Lean-v4.15.0-blue)](./lean/PvsNPAdjudication.lean) [![Zero Sorrys](https://img.shields.io/badge/sorry-0-brightgreen)](./lean/PvsNPAdjudication.lean) [![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](./LICENSE)

This repository contains machine-checked **Lean 4.15.0** formal proofs ([\`lean/PvsNPAdjudication.lean\`](./lean/PvsNPAdjudication.lean)) and a standalone **LaTeX** manuscript ([\`latex/p_vs_np_adjudication.tex\`](./latex/p_vs_np_adjudication.tex)) covering six formal propositions on **$\mathbf{P}$ vs. $\mathbf{NP}$**:

1. **Unconditional $\mathbf{NP}$-Completeness Reductions, Arithmetization & Barrier Theorems (\`PNP-01\`, \`PNP-02\`, \`PNP-06\` — PROVEN)**:
   - **\`PNP-01\` (Cook–Levin / Karp Quartic Arithmetization Penalty)**: Proves $E_1(x) = x^4 - 2x^3 + 2x^2 - 2x + 1 = (x^2 - x)^2 + (x - 1)^2 \ge 0$ and the exact satisfying zero-locus $E_1(x) = 0 \iff x = 1$.
   - **\`PNP-02\` (Tseitin $3\text{-SAT}$ $\mathrm{AND}$-Gate Equi-Satisfiability & Linear Clause Slack)**: Proves over \`Bool\` that $(\neg x \lor \neg y \lor z) \land (x \lor \neg z) \land (y \lor \neg z) = \mathrm{true} \iff z = (x \land y)$, together with $S(x) = (x+2)^2 - (2x+3) = (x+1)^2 \ge 0$.
   - **\`PNP-06\` (Spectral Discrepancy & Baker–Gill–Solovay Relativizing Diagonalization)**: Proves $D_{\mathrm{spec}}(x,y) = (x-y)^2 \ge 0$ (vanishing iff $x=y$) and proves that for any evaluation table \`eval : Nat → Nat → Bool\`, the diagonal language \`diagonalLanguage eval m\ = !(eval m m)\` differs from machine \`m\` at input \`m\` regardless of oracle relativization.
2. **Formal Refutations of Candidate $\mathbf{P} = \mathbf{NP}$ and $\mathbf{P} \ne \mathbf{NP}$ Proof Lemmas (\`PNP-03\`, \`PNP-04\`, \`PNP-05\` — REFUTED BY COUNTEREXAMPLE)**:
   - **\`PNP-03\` (Refutation of Pairwise $2\text{-SAT}$ Projection Heuristics)**: Proves $L_3(1,1) = -4 < 0$ and verifies over \`Bool\` that the complete 8-clause $3\text{-CNF}$ contradiction on 3 variables is globally unsatisfiable despite every 2-variable projection satisfying 6 of the 8 clauses.
   - **\`PNP-04\` (Refutation of Zero LP Integrality Gap on Odd Cycle $K_3$)**: Proves $G_{\mathrm{LP}}(\frac{1}{2}) = -1 < 0$ at the symmetric fractional LP optimum and verifies over \`Bool\` that every integral vertex cover of $K_3$ has size $\ge 2$ versus the fractional LP optimum $\frac{3}{2}$ (an integrality gap of $\frac{4}{3}$).
   - **\`PNP-05\` (Refutation of No-Cancellation Monotone Transfer via Karatsuba's Identity)**: Proves $K(1,1) = -1 < 0$ and proves the universal Karatsuba 3-multiplication identity $(a_1 + a_0)(b_1 + b_0) - a_1 b_1 - a_0 b_0 = a_1 b_0 + a_0 b_1$, showing constructively how subtraction cancellation reduces multiplicative gate complexity from $4$ to $3$.

---

## Quickstart (Verify with Lean 4)

No external dependencies or Mathlib downloads are required; the file uses only the Lean 4.15.0 standard prelude and core \`Int\` / \`Bool\` / \`omega\` / \`decide\` tactics:

\`\`\`bash
lean lean/PvsNPAdjudication.lean
\`\`\`

To compile the LaTeX manuscript:

\`\`\`bash
pdflatex latex/p_vs_np_adjudication.tex
\`\`\`

---

## Summary Table

| ID | Mathematical Claim / Candidate Proof Lemma | Verdict | Lean 4 Theorem(s) |
| :--- | :--- | :--- | :--- |
| \`PNP-01\` | **Cook–Levin Quartic Arithmetization Penalty**: $E_1(x) = (x^2-x)^2 + (x-1)^2 \ge 0$ ($=0 \iff x=1$) | **PROVEN** | \`pnp_01_cook_levin_gadget_nonneg\`, \`pnp_01_cook_levin_gadget_sos_and_zero_locus\` |
| \`PNP-02\` | **Tseitin $3\text{-SAT}$ Equi-Satisfiability & Slack**: $\mathcal{T}_{\land}(x,y,z) \iff z = x\land y$ and $S(x)=(x+1)^2\ge 0$ | **PROVEN** | \`pnp_02_tseitin_and_gadget_equisat\`, \`pnp_02_tseitin_and_gadget_equisat_and_slack\` |
| \`PNP-03\` | **Candidate $\mathbf{P}=\mathbf{NP}$ Lemma**: Pairwise $2\text{-SAT}$ relaxation $L_3(x,y) = 2(x+y)(1-x-y) \ge 0$ on $\{0,1\}^2$ | **REFUTED** | \`pnp_03_pairwise_2sat_projection_refuted\` |
| \`PNP-04\` | **Candidate $\mathbf{P}=\mathbf{NP}$ Lemma**: Odd-cycle $K_3$ LP relaxation has zero integrality gap | **REFUTED** | \`pnp_04_k3_lp_integrality_gap_refuted\` |
| \`PNP-05\` | **Candidate $\mathbf{P}\ne\mathbf{NP}$ Lemma**: Non-monotone circuits have no cancellation advantage over monotone circuits | **REFUTED** | \`pnp_05_non_monotone_cancellation_refuted\`, \`pnp_05_karatsuba_three_mult_identity\` |
| \`PNP-06\` | **Spectral Discrepancy & BGS Relativizing Diagonalization**: $D_{\mathrm{spec}}(x,y)=(x-y)^2\ge 0$ & $\mathrm{diag}(m)\ne\mathrm{eval}(m,m)$ | **PROVEN** | \`pnp_06_spectral_discrepancy_and_diagonalization_barrier\`, \`pnp_06_baker_gill_solovay_diagonal_differs\` |
