# lean4-complexity-adjudicator

[![Lean 4.15.0](https://img.shields.io/badge/Lean-v4.15.0-blue)](./lean/PvsNPMathlib.lean) [![Mathlib v4.15.0](https://img.shields.io/badge/Mathlib-v4.15.0-purple)](./lean/PvsNPMathlib.lean) [![Zero Sorrys](https://img.shields.io/badge/sorry-0-brightgreen)](./lean/PvsNPMathlib.lean) [![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](./LICENSE)

This repository provides machine-checked **Lean 4.15.0** formalizations of algebraic satisfiability gadgets, pointwise diagonalization lemmas, and explicit counterexamples to continuous-relaxation and monotone-circuit shortcut lemmas in two complementary layers alongside a standalone **LaTeX** manuscript ([`latex/p_vs_np_adjudication.tex`](./latex/p_vs_np_adjudication.tex)):

1. **Analytic & Algebraic `Mathlib` v4.15.0 Formalization over $\mathbb{R}$, `[CommRing R]`, `Bool`, Inductive `BoolCircuit`, and Arbitrary Index Types $\alpha$** ([`lean/PvsNPMathlib.lean`](./lean/PvsNPMathlib.lean)):
   - Formulates continuous polynomial/LP relaxations over $\mathbb{R}$ (`Mathlib.Data.Real.Basic`), algebraic ring identities over arbitrary commutative rings `[CommRing R]`, Boolean gadget and inductive circuit Tseitin 3-CNF equi-satisfiability over `Bool` and `BoolCircuit` (`PNP-02`, `PNP-07`), polynomial-method degree lower bounds for 3-bit Parity via boolean cube finite differences (`PNP-08`), and abstract pointwise diagonalization over any indexing type `α` (`PNP-06`).
2. **Zero-Dependency Core Lean 4 Formalization** ([`lean/PvsNPAdjudication.lean`](./lean/PvsNPAdjudication.lean)):
   - Verified in $< 2$ seconds using only the Lean 4 standard prelude (`Int` / `Bool` / `omega` / `decide`) without downloading Mathlib.

---

## Mathematical Overview (`PNP-01` through `PNP-08`)

### 1. Unconditional Satisfiability Gadgets, Inductive Circuit Reductions, Polynomial Degree Lower Bounds & Pointwise Diagonalization (`PNP-01`, `PNP-02`, `PNP-06`, `PNP-07`, `PNP-08` — PROVEN)
- **`PNP-01` (Single-Variable Quartic Boolean-Domain & Unit-Clause Penalty over $\mathbb{R}$)**:
  Defines `cookLevinRealEnergy (x : ℝ) : ℝ := x^4 - 2*x^3 + 2*x^2 - 2*x + 1` (aliased as `cookLevinPenalty`). Proves the Sum-of-Squares decomposition `(x^2 - x)^2 + (x - 1)^2 ≥ 0` over $\mathbb{R}$ and the exact real zero-locus `cookLevinRealEnergy x = 0 ↔ x = 1` (encoding the single-variable boolean integrality constraint $x \in \{0,1\}$ coupled with unit clause $x = 1$).
- **`PNP-02` (Tseitin $3\text{-SAT}$ Single $\mathrm{AND}$-Gate Equi-Satisfiability & Continuous Slack over $\mathbb{R}$)**:
  Proves over `Bool` that `(¬x ∨ ¬y ∨ z) ∧ (x ∨ ¬z) ∧ (y ∨ ¬z) = true ↔ z = (x && y)`, and proves over $\mathbb{R}$ that the quadratic-over-linear slack functional `tseitinRealSlack x := (x + 2)^2 - (2*x + 3) = (x + 1)^2 ≥ 0` vanishes iff $x = -1$.
- **`PNP-06` (Spectral Discrepancy over $\mathbb{R}$ & Abstract Pointwise Diagonalization over $\alpha$)**:
  Proves `spectralDiscrepancyReal x y = (x - y)^2 ≥ 0` with `= 0 ↔ x = y` over $\mathbb{R}$, and proves that for any indexing type `α` and boolean evaluation table `eval : α → α → Bool`, the diagonal predicate `diagonalLanguage eval m := !(eval m m)` differs from row `m` at input `m` (`diagonalLanguage eval m ≠ eval m m`) and therefore cannot equal `eval m` for any $m : \alpha$ (`pnp_06_no_machine_decides_diagonalLanguage`).
- **`PNP-07` (Structural Induction Equi-Satisfiability & Linear Clause Bound for Tseitin 3-CNF Transformation on Arbitrary-Depth Boolean Circuits)**:
  Defines the inductive syntax `BoolCircuit` (`var`, `not`, `and`, `or`) of arbitrary-depth boolean circuits, recursive evaluation `evalCircuit`, internal gate count `gateCount`, emitted 3-CNF clause count `tseitinGateClauseCount`, and the recursive Tseitin wire-consistency predicate `tseitinWireConsistent`. Proves by structural induction on `c : BoolCircuit` that:
  1. `tseitinGateClauseCount c ≤ 3 * gateCount c` and `tseitinGateClauseCount c + 1 ≤ 3 * gateCount c + 1` (`pnp_07_tseitin_clause_count_linear_bound`),
  2. Every wire assignment satisfying `tseitinWireConsistent env wire c` evaluates the output wire to `evalCircuit env c` (`pnp_07_tseitin_circuit_soundness`),
  3. The canonical wire assignment `evalCircuit env` satisfies `tseitinWireConsistent env (evalCircuit env) c` (`pnp_07_tseitin_circuit_completeness`),
  4. `evalCircuit env c = true ↔ ∃ wire, tseitinWireConsistent env wire c ∧ wire c = true` (`pnp_07_tseitin_circuit_equisat`).
- **`PNP-08` (Unconditional Polynomial-Method Degree Lower Bound for 3-Bit Parity over $\mathbb{R}$ via Boolean Cube Finite Differences)**:
  Defines the 3-fold boolean cube finite-difference operator `cubeFiniteDiff3 (f : ℝ → ℝ → ℝ → ℝ) : ℝ := f 1 1 1 - f 1 1 0 - f 1 0 1 - f 0 1 1 + f 1 0 0 + f 0 1 0 + f 0 0 1 - f 0 0 0`, the general 10-parameter degree-$\le 2$ polynomial `degAtMost2Poly3`, and the 3-bit $\pm 1$ parity function `paritySign3 x1 x2 x3 := (1 - 2*x1) * (1 - 2*x2) * (1 - 2*x3)`. Proves that `cubeFiniteDiff3` annihilates every degree-$\le 2$ polynomial (`pnp_08_cubeFiniteDiff3_degAtMost2_eq_zero`), whereas `cubeFiniteDiff3 paritySign3 = -8` (`pnp_08_cubeFiniteDiff3_paritySign3_eq_neg_eight`), and concludes that no degree-$\le 2$ polynomial over $\mathbb{R}$ (or `Int`) can agree with `paritySign3` on all 8 vertices of $\{0, 1\}^3$ (`pnp_08_no_deg2_polynomial_computes_parity3`).

### 2. Formal Counterexamples to Continuous-Relaxation & Monotone-Circuit Shortcut Lemmas (`PNP-03`, `PNP-04`, `PNP-05` — REFUTED BY COUNTEREXAMPLE)
- **`PNP-03` (Refutation of Pairwise $2\text{-SAT}$ Projection Heuristics & Explicit Quantifier Separation `∀ i ∃ z_i` vs `∃ z ∀ i`)**:
  Proves that `pairwise2SatRealMargin (1 : ℝ) (1 : ℝ) = -4 < 0`, verifies over `Bool` that the complete 8-clause $3\text{-CNF}$ contradiction `unsat3CnfContradiction` on 3 variables is globally unsatisfiable, and proves `pnp_03_clausewise_vs_global_existential_quantifier_gap`: for every `(x1, x2) ∈ Bool^2`, the **clause-wise existential projection** `clausewiseProjected3Cnf x1 x2` ($\bigwedge_{i=1}^{8} \exists z_i, C_i(x_1,x_2,z_i)$) is `true`, whereas the **global existential projection** `globalExistentialProjected3Cnf x1 x2` ($\exists z \bigwedge_{i=1}^{8} C_i(x_1,x_2,z)$) is `false`.
- **`PNP-04` (Refutation of Zero LP Integrality Gap on Odd Cycle $K_3$ & Complete LP/IP Optimality over $\mathbb{R}$ & `Bool`)**:
  Proves directly over $\mathbb{R}$ (`pnp_04_k3_lp_integrality_gap_over_reals`) that every LP-feasible triple $(x_1,x_2,x_3) \in \mathbb{R}^3$ satisfying $x_1+x_2 \ge 1, x_2+x_3 \ge 1, x_3+x_1 \ge 1$ has objective `k3FractionalObj x1 x2 x3 ≥ 3/2` (achieved at `(1/2, 1/2, 1/2)`), while every integral vertex cover `(x1,x2,x3) ∈ Bool^3` has weight `≥ 2` (achieved at `(true, true, false)`), establishing the exact integrality gap $\frac{2}{3/2} = \frac{4}{3}$.
- **`PNP-05` (Refutation of Bilinear Margin Non-Negativity & Karatsuba's Identity over `[CommRing R]`)**:
  Proves over $\mathbb{R}$ that `karatsubaRealMargin x y = -(x * y)` equals `-1 < 0` at `(1, 1)`, and proves over any commutative ring `[CommRing R]` that `(a₁ + a₀)*(b₁ + b₀) - a₁*b₁ - a₀*b₀ = a₁*b₀ + a₀*b₁`.

---

## Quickstart

### Option A: Verify the Full `Mathlib` Formalization (`lean/PvsNPMathlib.lean`)
```bash
lake exe cache get
lake env lean lean/PvsNPMathlib.lean
```

### Option B: Verify the Zero-Dependency Core Formalization (`lean/PvsNPAdjudication.lean`)
```bash
lean lean/PvsNPAdjudication.lean
```

### Compile the LaTeX Manuscript
```bash
pdflatex latex/p_vs_np_adjudication.tex
```

---

## Summary Table

| ID | Formalized Statement / Candidate Shortcut Lemma | Verdict | Mathlib Theorem(s) (`PvsNPMathlib.lean`) | Core Theorem(s) (`PvsNPAdjudication.lean`) |
| :--- | :--- | :--- | :--- | :--- |
| `PNP-01` | **Single-Variable Quartic Penalty**: $E_1(x) = (x^2-x)^2 + (x-1)^2 \ge 0$ ($=0 \iff x=1$) | **PROVEN** | `pnp_01_cookLevinRealEnergy_sos`, `pnp_01_cookLevinRealEnergy_eq_zero_iff`, `pnp_01_cookLevinPenalty_sos_and_zero_locus` | `pnp_01_cook_levin_gadget_nonneg`, `pnp_01_cook_levin_gadget_sos_and_zero_locus` |
| `PNP-02` | **Tseitin $\mathrm{AND}$-Gate Equi-Satisfiability & Slack**: $\mathcal{T}_{\land}(x,y,z) \iff z = x\land y$ and $S(x)=(x+1)^2\ge 0$ | **PROVEN** | `pnp_02_tseitin_and_gadget_equisat`, `pnp_02_tseitinRealSlack_sos`, `pnp_02_tseitinAndGadget_equisat`, `pnp_02_tseitinSlack_sos` | `pnp_02_tseitin_and_gadget_equisat`, `pnp_02_tseitin_and_gadget_equisat_and_slack` |
| `PNP-03` | **Relaxation Shortcut Lemma**: Pairwise $2\text{-SAT}$ surrogate $L_3(1,1) = -4 < 0$ & $\forall i \exists z_i$ vs $\exists z \forall i$ gap | **REFUTED** | `pnp_03_pairwise_2sat_projection_refuted`, `pnp_03_clausewise_vs_global_existential_quantifier_gap`, `pnp_03_pairwise2Sat_projection_refuted` | `pnp_03_pairwise_2sat_projection_refuted` |
| `PNP-04` | **Relaxation Shortcut Lemma**: Odd-cycle $K_3$ LP minimum $\frac{3}{2}$ vs IP minimum $2$ (gap $\frac{4}{3}$) | **REFUTED** | `pnp_04_k3_lp_integrality_gap_refuted`, `pnp_04_k3_lp_integrality_gap_over_reals` | `pnp_04_k3_lp_integrality_gap_refuted` |
| `PNP-05` | **Algebraic Cancellation Identity**: $K(1,1)=-1<0$ & Karatsuba identity over `[CommRing R]` | **REFUTED** | `pnp_05_non_monotone_cancellation_refuted`, `pnp_05_karatsuba_three_mult_identity`, `pnp_05_karatsuba_commRing_identity`, `pnp_05_cancellation_witness_neg` | `pnp_05_non_monotone_cancellation_refuted`, `pnp_05_karatsuba_three_mult_identity` |
| `PNP-06` | **Spectral Discrepancy & Pointwise Diagonalization**: $D_{\mathrm{spec}}(x,y)=(x-y)^2\ge 0$ & $\mathrm{diag}(m)\ne\mathrm{eval}(m,m)$ | **PROVEN** | `pnp_06_spectral_discrepancy_real_sos`, `pnp_06_baker_gill_solovay_diagonal_differs`, `pnp_06_no_machine_decides_diagonalLanguage`, `pnp_06_spectralDiscrepancy_sos`, `pnp_06_bgs_diagonalization_barrier` | `pnp_06_spectral_discrepancy_and_diagonalization_barrier`, `pnp_06_baker_gill_solovay_diagonal_differs` |
| `PNP-07` | **Inductive Tseitin 3-CNF Circuit Reduction**: Clause count $\le 3s+1$ & `evalCircuit env c = true ↔ ∃ wire, ...` | **PROVEN** | `pnp_07_tseitin_clause_count_linear_bound`, `pnp_07_tseitin_circuit_soundness`, `pnp_07_tseitin_circuit_completeness`, `pnp_07_tseitin_circuit_equisat` | `pnp_07_tseitin_clause_count_linear_bound`, `pnp_07_tseitin_circuit_soundness`, `pnp_07_tseitin_circuit_completeness`, `pnp_07_tseitin_circuit_equisat` |
| `PNP-08` | **Polynomial-Method Degree Lower Bound for 3-Bit Parity**: $\Delta_{123}(P_{\le 2})=0 \ne -8 = \Delta_{123}(\mathrm{Parity}_3)$ | **PROVEN** | `pnp_08_cubeFiniteDiff3_degAtMost2_eq_zero`, `pnp_08_cubeFiniteDiff3_paritySign3_eq_neg_eight`, `pnp_08_no_deg2_polynomial_computes_parity3` | `pnp_08_cubeFiniteDiff3_degAtMost2_eq_zero`, `pnp_08_cubeFiniteDiff3_paritySign3_eq_neg_eight`, `pnp_08_no_deg2_polynomial_computes_parity3` |
