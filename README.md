# lean4-complexity-adjudicator

[![Lean 4.15.0](https://img.shields.io/badge/Lean-v4.15.0-blue)](./lean/PvsNPMathlib.lean) [![Mathlib v4.15.0](https://img.shields.io/badge/Mathlib-v4.15.0-purple)](./lean/PvsNPMathlib.lean) [![Zero Sorrys](https://img.shields.io/badge/sorry-0-brightgreen)](./lean/PvsNPMathlib.lean) [![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](./LICENSE)

This repository provides machine-checked **Lean 4.15.0** formalizations of algebraic satisfiability gadgets, an inductive arbitrary-depth Boolean circuit-to-3CNF compiler (`compileTseitinCNF`) with verified clause-list length bounds, asymptotic all-$n$ hypercube Fourier/polynomial degree lower bounds for $n$-bit Parity, Razborov–Rudich Natural Proofs and Aaronson–Wigderson algebrization barrier inequalities, pointwise diagonalization lemmas, and explicit counterexamples to continuous-relaxation shortcut lemmas in two complementary layers alongside a standalone **LaTeX** manuscript ([`latex/p_vs_np_adjudication.tex`](./latex/p_vs_np_adjudication.tex)):

1. **Analytic & Algebraic `Mathlib` v4.15.0 Formalization over $\mathbb{R}$, `[CommRing R]`, `Bool`, Inductive `BoolCircuit`, and Arbitrary Dimension $n : \mathbb{N}$** ([`lean/PvsNPMathlib.lean`](./lean/PvsNPMathlib.lean)):
   - Formulates continuous polynomial/LP relaxations over $\mathbb{R}$ (`Mathlib.Data.Real.Basic`), algebraic ring identities over arbitrary commutative rings `[CommRing R]`, Boolean gadget and concrete emitted `List (Clause3 BoolCircuit)` Tseitin 3-CNF equi-satisfiability (`PNP-02`, `PNP-07`), asymptotic all-$n$ polynomial-method degree lower bounds for $n$-bit Parity (`PNP-08`), Razborov–Rudich Natural Proofs and algebrization extension obstructions (`PNP-09`), and abstract pointwise diagonalization over any indexing type `α` (`PNP-06`).
2. **Zero-Dependency Core Lean 4 Formalization** ([`lean/PvsNPAdjudication.lean`](./lean/PvsNPAdjudication.lean)):
   - Verified in $< 5$ seconds using only the Lean 4 standard prelude (`Int` / `Bool` / `List` / `omega` / `decide`) without downloading Mathlib.

---

## Mathematical Overview (`PNP-01` through `PNP-09`)

### 1. Unconditional Satisfiability Gadgets, Emitted Tseitin 3-CNF Compiler, Asymptotic All-$n$ Parity Degree Lower Bounds & Meta-Complexity Barriers (`PNP-01`, `PNP-02`, `PNP-06`, `PNP-07`, `PNP-08`, `PNP-09` — PROVEN)
- **`PNP-01` (Single-Variable Quartic Boolean-Domain & Unit-Clause Penalty over $\mathbb{R}$)**:
  Defines `cookLevinRealEnergy (x : ℝ) : ℝ := x^4 - 2*x^3 + 2*x^2 - 2*x + 1` (aliased as `cookLevinPenalty`). Proves the Sum-of-Squares decomposition `(x^2 - x)^2 + (x - 1)^2 ≥ 0` over $\mathbb{R}$ and the exact real zero-locus `cookLevinRealEnergy x = 0 ↔ x = 1`.
- **`PNP-02` (Tseitin $3\text{-SAT}$ Single $\mathrm{AND}$-Gate Equi-Satisfiability & Continuous Slack over $\mathbb{R}$)**:
  Proves over `Bool` that `(¬x ∨ ¬y ∨ z) ∧ (x ∨ ¬z) ∧ (y ∨ ¬z) = true ↔ z = (x && y)`, and proves over $\mathbb{R}$ that `tseitinRealSlack x := (x + 2)^2 - (2*x + 3) = (x + 1)^2 ≥ 0` vanishes iff $x = -1$.
- **`PNP-06` (Spectral Discrepancy over $\mathbb{R}$ & Abstract Pointwise Diagonalization over $\alpha$)**:
  Proves `spectralDiscrepancyReal x y = (x - y)^2 ≥ 0` with `= 0 ↔ x = y` over $\mathbb{R}$, and proves that for any indexing type `α` and boolean evaluation table `eval : α → α → Bool`, `diagonalLanguage eval m := !(eval m m)` differs from `eval m m` (`pnp_06_no_machine_decides_diagonalLanguage`).
- **`PNP-07` (Concrete Emitted `List (Clause3 BoolCircuit)` Tseitin 3-CNF Compiler, Verified Clause-List Length Bound $\le 3s + 1$, Strict $\mathrm{NOT}$-Gate Inequality, and Equi-Satisfiability)**:
  Defines the inductive syntax `BoolCircuit` (`var`, `not`, `and`, `or`), recursive evaluation `evalCircuit`, `nodeId`, `canonicalWireEnv`, internal gate count `gateCount`, gate clause count `tseitinGateClauseCount` (counting $2$ clauses per `not` gate and $3$ clauses per `and`/`or` gate), and the concrete 3-CNF compiler `compileTseitinCNF : BoolCircuit → List (Clause3 BoolCircuit)` evaluated via `evalCNF3` and `tseitin3CNFSat`. Proves by structural induction on `c : BoolCircuit` that:
  1. `(compileTseitinGateClauses c).length = tseitinGateClauseCount c` (`pnp_07_emitted_gate_clauses_length`),
  2. `(compileTseitinCNF c).length = tseitinGateClauseCount c + 1` and `(compileTseitinCNF c).length ≤ 3 * gateCount c + 1` (`pnp_07_emitted_cnf_length_bound`, `pnp_07_tseitin_clause_count_linear_bound`),
  3. For a single `not` gate `.not (.var 0)`, `(compileTseitinCNF (.not (.var 0))).length = 3 < 4 = 3 * gateCount (.not (.var 0)) + 1` (`pnp_07_single_not_gate_clause_count_strict_lt`), showing the upper bound $3s + 1$ is a strict inequality whenever a `not` gate is present,
  4. Full soundness, completeness, and global equi-satisfiability both for `tseitinWireConsistent` (`pnp_07_tseitin_circuit_soundness`, `pnp_07_tseitin_circuit_completeness`, `pnp_07_tseitin_circuit_equisat`, `pnp_07_mathlib_tseitin_equisat_and_size`) and for the concrete emitted clause list (`pnp_07_emitted_cnf_equisat`).
- **`PNP-08` (Asymptotic All-$n$ Hypercube Fourier/Polynomial Degree Lower Bound for $n$-Bit Parity over $\mathbb{R}$ and `Int`)**:
  1. **Fixed $n = 3$ Certificate**: Proves `cubeFiniteDiff3` (and `realCubeFiniteDiff3`) annihilates every 10-parameter degree-$\le 2$ polynomial (`pnp_08_cubeFiniteDiff3_degAtMost2_eq_zero`, `pnp_08_real_cubeFiniteDiff3_degAtMost2_eq_zero`), whereas `cubeFiniteDiff3 paritySign3 = -8` (`pnp_08_cubeFiniteDiff3_paritySign3_eq_neg_eight`), so no degree-$\le 2$ polynomial computes 3-bit Parity on $\{0,1\}^3$ (`pnp_08_no_deg2_polynomial_computes_parity3`, `pnp_08_mathlib_no_real_deg2_polynomial_computes_parity3`).
  2. **Asymptotic Arbitrary-$n$ (`n : Nat`) Hypercube Theorem**: Defines the $n$-bit Parity sign function `paritySignN` / `paritySignRealN` and the $n$-dimensional hypercube Fourier parity functional `hypercubeFourierParityN` / `realHypercubeFourierParityN` for all $n \in \mathbb{N}$. Proves by induction on $n \in \mathbb{N}$ that:
     - `realHypercubeFourierParityN n (paritySignRealN n) = 2^n > 0` (`pnp_08_all_n_real_parity_fourier_eq_two_pow`, `pnp_08_all_n_parity_fourier_pos`),
     - Every sub-degree term `f` independent of at least one coordinate $k < n$ (including every multilinear monomial of degree $\le n - 1$) satisfies $\Delta_n(f) = 0$ (`pnp_08_all_n_subdegree_term_annihilated`, `pnp_08_all_n_real_subdegree_term_annihilated`),
     - Consequently, for **every $n \in \mathbb{N}$**, no finite sum of sub-degree terms `sumPolyTerms terms` / `sumRealPolyTerms terms` (i.e., no polynomial of degree $< n$) can compute $n$-bit Parity on $\{0,1\}^n$ (`pnp_08_all_n_no_subdegree_polynomial_computes_parity`, `pnp_08_all_n_real_no_subdegree_polynomial_computes_parity`).
- **`PNP-09` (Razborov–Rudich Natural Proofs Distinguisher Inequality & Aaronson–Wigderson Algebrization Extension Obstruction)**:
  Proves that any combinatorial property satisfying **Largeness** (`prob_C ≥ delta`) and **Usefulness** against a function family `F` (`prob_F = 0`) achieves pseudorandomness distinguishing advantage `|prob_C - prob_F| ≥ delta`, forcing `delta ≤ eps` under any PRF security bound `≤ eps` (`pnp_09_razborov_rudich_natural_proofs_barrier`, `pnp_09_mathlib_razborov_rudich_natural_proofs_barrier`), and proves that the boolean-idempotence polynomial $x^2 - x$ vanishes on $\{0,1\}$ yet evaluates to $2 \ne 0$ at $x = 2$ (`pnp_09_algebrization_extension_obstruction`, `pnp_09_mathlib_algebrization_extension_obstruction`).

### 2. Formal Counterexamples to Continuous-Relaxation & Monotone-Circuit Shortcut Lemmas (`PNP-03`, `PNP-04`, `PNP-05` — REFUTED BY COUNTEREXAMPLE)
- **`PNP-03`**: Explicit quantifier separation between satisfiable clause-wise projection `clausewiseProjected3Cnf` ($\bigwedge_i \exists z_i$) and unsatisfiable exact existential projection `globalExistentialProjected3Cnf` ($\exists z \bigwedge_i$) on the 8-clause 3-SAT contradiction (`pnp_03_clausewise_vs_global_existential_quantifier_gap`).
- **`PNP-04`**: Complete LP ($\ge 3/2$, attained at $(1/2,1/2,1/2)$) vs IP ($\ge 2$, attained at $(1,1,0)$) optimality and $4/3$ integrality gap on $K_3$ (`pnp_04_k3_lp_integrality_gap_over_reals`).
- **`PNP-05`**: Bilinear cancellation identity $(a_1+a_0)(b_1+b_0) - a_1 b_1 - a_0 b_0 = a_1 b_0 + a_0 b_1$ over `[CommRing R]` (`pnp_05_karatsuba_three_mult_identity`).

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
| `PNP-07` | **Emitted `List Clause3` Tseitin 3-CNF Compiler**: `(compileTseitinCNF c).length = tseitinGateClauseCount c + 1 ≤ 3s + 1` ($3 < 4$ for single `not`) & Equi-Sat | **PROVEN** | `pnp_07_tseitin_clause_count_linear_bound`, `pnp_07_tseitin_circuit_soundness`, `pnp_07_tseitin_circuit_completeness`, `pnp_07_tseitin_circuit_equisat`, `pnp_07_emitted_gate_clauses_length`, `pnp_07_single_not_gate_clause_count_strict_lt`, `pnp_07_mathlib_tseitin_equisat_and_size` | `pnp_07_tseitin_clause_count_linear_bound`, `pnp_07_tseitin_circuit_soundness`, `pnp_07_tseitin_circuit_completeness`, `pnp_07_tseitin_circuit_equisat`, `pnp_07_emitted_gate_clauses_length`, `pnp_07_emitted_cnf_length_bound`, `pnp_07_single_not_gate_clause_count_strict_lt`, `pnp_07_emitted_cnf_equisat` |
| `PNP-08` | **Asymptotic All-$n$ & 3-Bit Parity Polynomial Degree Lower Bound**: $\Delta_n(P_{<n})=0 \ne 2^n = \Delta_n(\chi_n)$ for all $n \in \mathbb{N}$ | **PROVEN** | `pnp_08_cubeFiniteDiff3_degAtMost2_eq_zero`, `pnp_08_real_cubeFiniteDiff3_degAtMost2_eq_zero`, `pnp_08_cubeFiniteDiff3_paritySign3_eq_neg_eight`, `pnp_08_no_deg2_polynomial_computes_parity3`, `pnp_08_mathlib_no_real_deg2_polynomial_computes_parity3`, `pnp_08_all_n_real_subdegree_term_annihilated`, `pnp_08_all_n_real_parity_fourier_eq_two_pow`, `pnp_08_all_n_real_no_subdegree_polynomial_computes_parity` | `pnp_08_cubeFiniteDiff3_degAtMost2_eq_zero`, `pnp_08_cubeFiniteDiff3_paritySign3_eq_neg_eight`, `pnp_08_no_deg2_polynomial_computes_parity3`, `pnp_08_all_n_subdegree_term_annihilated`, `pnp_08_all_n_parity_fourier_pos`, `pnp_08_all_n_subdegree_sum_eq_zero`, `pnp_08_all_n_no_subdegree_polynomial_computes_parity` |
| `PNP-09` | **Razborov–Rudich Natural Proofs & Algebrization Extension Obstruction**: $\delta \le \varepsilon$ PRF bound & $2^2 - 2 = 2 \ne 0$ | **PROVEN** | `pnp_09_mathlib_razborov_rudich_natural_proofs_barrier`, `pnp_09_mathlib_algebrization_extension_obstruction` | `pnp_09_razborov_rudich_natural_proofs_barrier`, `pnp_09_algebrization_extension_obstruction` |
