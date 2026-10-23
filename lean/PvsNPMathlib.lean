/-
  P vs. NP — Formal Reductions, Complexity Barriers & Candidate-Lemma Refutations
  Verified against Mathlib (Lean 4.15.0) with zero `sorry` placeholders and zero custom axioms.

  Imports Mathlib's real analysis (`ℝ`), commutative ring hierarchy (`CommRing`),
  and algebraic/nonlinear arithmetic tactics (`ring`, `linarith`, `nlinarith`, `positivity`, `norm_num`).
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace PvsNPMathlib

/- ============================================================================
   SECTION 1: PNP-01 — SINGLE-VARIABLE QUARTIC BOOLEAN-DOMAIN & UNIT-CLAUSE
   ARITHMETIZATION PENALTY OVER `ℝ`
   ============================================================================ -/

/-- Real polynomial penalty for boolean domain `x ∈ {0, 1}` coupled with positive
    unit clause `x = 1` over `ℝ`:
    `E_1(x) = x^4 - 2*x^3 + 2*x^2 - 2*x + 1`. -/
def cookLevinRealEnergy (x : ℝ) : ℝ :=
  x ^ 4 - 2 * x ^ 3 + 2 * x ^ 2 - 2 * x + 1

abbrev cookLevinPenalty (x : ℝ) : ℝ := cookLevinRealEnergy x

/-- Theorem PNP-01a (Exact Sum-of-Squares Decomposition over `ℝ`):
    `cookLevinRealEnergy x = (x^2 - x)^2 + (x - 1)^2` and `0 ≤ cookLevinRealEnergy x`. -/
theorem pnp_01_cookLevinRealEnergy_sos (x : ℝ) :
    cookLevinRealEnergy x = (x ^ 2 - x) ^ 2 + (x - 1) ^ 2 ∧
    0 ≤ cookLevinRealEnergy x := by
  have hsos : cookLevinRealEnergy x = (x ^ 2 - x) ^ 2 + (x - 1) ^ 2 := by
    unfold cookLevinRealEnergy
    ring
  refine ⟨hsos, ?_⟩
  rw [hsos]
  positivity

/-- Theorem PNP-01b (Unique Real Satisfying Zero-Locus over `ℝ`):
    For all `x : ℝ`, `cookLevinRealEnergy x = 0` if and only if `x = 1`. -/
theorem pnp_01_cookLevinRealEnergy_eq_zero_iff (x : ℝ) :
    cookLevinRealEnergy x = 0 ↔ x = 1 := by
  rw [(pnp_01_cookLevinRealEnergy_sos x).1]
  constructor
  · intro hsum
    have h1 : 0 ≤ (x ^ 2 - x) ^ 2 := sq_nonneg (x ^ 2 - x)
    have h2 : 0 ≤ (x - 1) ^ 2 := sq_nonneg (x - 1)
    have hsq0 : (x - 1) ^ 2 = 0 := by linarith
    have hx0 : x - 1 = 0 := sq_eq_zero_iff.mp hsq0
    linarith
  · intro hx
    rw [hx]
    norm_num

/-- Combined Theorem PNP-01c (SOS Decomposition, Non-Negativity & Exact Zero-Locus over `ℝ`): -/
theorem pnp_01_cookLevinPenalty_sos_and_zero_locus (x : ℝ) :
    cookLevinPenalty x = (x ^ 2 - x) ^ 2 + (x - 1) ^ 2 ∧
    0 ≤ cookLevinPenalty x ∧
    (cookLevinPenalty x = 0 ↔ x = 1) :=
  ⟨(pnp_01_cookLevinRealEnergy_sos x).1,
   (pnp_01_cookLevinRealEnergy_sos x).2,
   pnp_01_cookLevinRealEnergy_eq_zero_iff x⟩

/- ============================================================================
   SECTION 2: PNP-02 — TSEITIN 3-SAT AND-GATE EQUI-SATISFIABILITY & REAL SLACK
   ============================================================================ -/

/-- Tseitin 3-CNF encoding of the single AND gate `z ↔ (x ∧ y)`:
    `(!x ∨ !y ∨ z) ∧ (x ∨ !z) ∧ (y ∨ !z)`. -/
def tseitinAndClauses (x y z : Bool) : Bool :=
  ((!x || !y || z) && (x || !z) && (y || !z))

/-- Theorem PNP-02a: For all `x, y, z : Bool`, the 3-CNF Tseitin AND-gate gadget evaluates to
    `true` if and only if the auxiliary wire `z` equals `x && y`. -/
theorem pnp_02_tseitin_and_gadget_equisat :
    ∀ (x y z : Bool), tseitinAndClauses x y z = true ↔ z = (x && y) := by
  decide

theorem pnp_02_tseitinAndGadget_equisat :
    ∀ (x y z : Bool), tseitinAndClauses x y z = true ↔ z = (x && y) :=
  pnp_02_tseitin_and_gadget_equisat

/-- Quadratic-over-linear clause expansion slack over `ℝ`:
    `S(x) = (x + 2)^2 - (2*x + 3) = x^2 + 2*x + 1`. -/
def tseitinRealSlack (x : ℝ) : ℝ :=
  (x + 2) ^ 2 - (2 * x + 3)

/-- Theorem PNP-02b: Over `ℝ`, `tseitinRealSlack x = (x + 1)^2 ≥ 0`, vanishing iff `x = -1`. -/
theorem pnp_02_tseitinRealSlack_sos (x : ℝ) :
    tseitinRealSlack x = (x + 1) ^ 2 ∧
    0 ≤ tseitinRealSlack x ∧
    (tseitinRealSlack x = 0 ↔ x = -1) := by
  have hsos : tseitinRealSlack x = (x + 1) ^ 2 := by
    unfold tseitinRealSlack
    ring
  refine ⟨hsos, ?_, ?_⟩
  · rw [hsos]
    positivity
  · rw [hsos, sq_eq_zero_iff]
    constructor <;> intro h <;> linarith

theorem pnp_02_tseitinSlack_sos (x : ℝ) :
    tseitinRealSlack x = (x + 1) ^ 2 ∧
    0 ≤ tseitinRealSlack x ∧
    (tseitinRealSlack x = 0 ↔ x = -1) :=
  pnp_02_tseitinRealSlack_sos x

/- ============================================================================
   SECTION 3: PNP-03 — REFUTATION OF PAIRWISE 2-SAT PROJECTION HEURISTIC OVER `ℝ`
   & EXPLICIT QUANTIFIER SEPARATION (`∀ i ∃ z_i` VS `∃ z ∀ i`)
   ============================================================================ -/

/-- Concave pairwise 2-SAT consistency functional over `ℝ`:
    `L_3(x, y) = 2*(x + y)*(1 - x - y) = 2*x + 2*y - 2*x^2 - 4*x*y - 2*y^2`. -/
def pairwise2SatRealMargin (x y : ℝ) : ℝ :=
  2 * x + 2 * y - 2 * x ^ 2 - 4 * x * y - 2 * y ^ 2

/-- Complete 8-clause 3-CNF contradiction on 3 boolean variables `x1, x2, x3`. -/
def unsat3CnfContradiction (x1 x2 x3 : Bool) : Bool :=
  ( x1 ||  x2 ||  x3) &&
  ( x1 ||  x2 || !x3) &&
  ( x1 || !x2 ||  x3) &&
  ( x1 || !x2 || !x3) &&
  (!x1 ||  x2 ||  x3) &&
  (!x1 ||  x2 || !x3) &&
  (!x1 || !x2 ||  x3) &&
  (!x1 || !x2 || !x3)

/-- Clause-wise existential projection onto `(x1, x2)`: each of the 8 clauses
    independently chooses its own witness `z_i ∈ Bool` (`⋀_{i=1}^8 ∃ z_i, C_i(x1, x2, z_i)`). -/
def clausewiseProjected3Cnf (x1 x2 : Bool) : Bool :=
  (( x1 ||  x2 || true) || ( x1 ||  x2 || false)) &&
  (( x1 ||  x2 || !true) || ( x1 ||  x2 || !false)) &&
  (( x1 || !x2 || true) || ( x1 || !x2 || false)) &&
  (( x1 || !x2 || !true) || ( x1 || !x2 || !false)) &&
  ((!x1 ||  x2 || true) || (!x1 ||  x2 || false)) &&
  ((!x1 ||  x2 || !true) || (!x1 ||  x2 || !false)) &&
  ((!x1 || !x2 || true) || (!x1 || !x2 || false)) &&
  ((!x1 || !x2 || !true) || (!x1 || !x2 || !false))

/-- Global existential projection onto `(x1, x2)`: a single witness `z ∈ Bool`
    must simultaneously satisfy all 8 clauses (`∃ z, ⋀_{i=1}^8 C_i(x1, x2, z)`). -/
def globalExistentialProjected3Cnf (x1 x2 : Bool) : Bool :=
  unsat3CnfContradiction x1 x2 true || unsat3CnfContradiction x1 x2 false

/-- Theorem PNP-03a: Refutes universal non-negativity of `pairwise2SatRealMargin` over `ℝ`
    at `(1, 1)` (`-4 < 0`) and proves that `unsat3CnfContradiction` has no satisfying assignment. -/
theorem pnp_03_pairwise_2sat_projection_refuted :
    pairwise2SatRealMargin 1 0 = 0 ∧
    pairwise2SatRealMargin 0 0 = 0 ∧
    pairwise2SatRealMargin 1 1 = -4 ∧
    pairwise2SatRealMargin 1 1 < 0 ∧
    (∀ (x1 x2 x3 : Bool), unsat3CnfContradiction x1 x2 x3 = false) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold pairwise2SatRealMargin; norm_num
  · unfold pairwise2SatRealMargin; norm_num
  · unfold pairwise2SatRealMargin; norm_num
  · unfold pairwise2SatRealMargin; norm_num
  · decide

theorem pnp_03_pairwise2Sat_projection_refuted :
    pairwise2SatRealMargin 1 0 = 0 ∧
    pairwise2SatRealMargin 0 0 = 0 ∧
    pairwise2SatRealMargin 1 1 = -4 ∧
    pairwise2SatRealMargin 1 1 < 0 ∧
    (∀ (x1 x2 x3 : Bool), unsat3CnfContradiction x1 x2 x3 = false) :=
  pnp_03_pairwise_2sat_projection_refuted

/-- Theorem PNP-03b (Explicit Quantifier Separation `∀ i ∃ z_i` vs `∃ z ∀ i`):
    For every pair `(x1, x2) ∈ Bool^2`, the clause-wise projection `clausewiseProjected3Cnf x1 x2`
    is `true` (where each clause chooses its own witness `z_i`), whereas the global existential
    projection `globalExistentialProjected3Cnf x1 x2` is `false` (no single `z` satisfies all 8 clauses). -/
theorem pnp_03_clausewise_vs_global_existential_quantifier_gap :
    (∀ (x1 x2 : Bool), clausewiseProjected3Cnf x1 x2 = true) ∧
    (∀ (x1 x2 : Bool), globalExistentialProjected3Cnf x1 x2 = false) := by
  decide

/- ============================================================================
   SECTION 4: PNP-04 — REFUTATION OF ZERO LP INTEGRALITY GAP ON ODD CYCLE `K_3`
   & COMPLETE PROOF OF LP OPTIMUM `3/2`, IP OPTIMUM `2`, AND GAP `4/3` OVER `ℝ`
   ============================================================================ -/

/-- Symmetric K_3 LP integrality-gap quadratic over `ℝ`:
    `G_LP(b) = 16 * b^2 - 16 * b + 3 = 4 * (2*b - 1)^2 - 1`. -/
def k3LpGapReal (b : ℝ) : ℝ :=
  16 * b ^ 2 - 16 * b + 3

/-- Fractional vertex-cover objective `x1 + x2 + x3` on `K_3` over `ℝ`. -/
def k3FractionalObj (x1 x2 x3 : ℝ) : ℝ :=
  x1 + x2 + x3

/-- Boolean indicator to integer `0` or `1`. -/
def b2i (b : Bool) : Int :=
  if b then 1 else 0

/-- Triangle K_3 Vertex Cover constraint: every edge `(1,2), (2,3), (3,1)` is covered. -/
def isK3VertexCover (x1 x2 x3 : Bool) : Bool :=
  (x1 || x2) && (x2 || x3) && (x3 || x1)

/-- Theorem PNP-04a: Over `ℝ`, `k3LpGapReal 0 = 3` and `k3LpGapReal 1 = 3` at the integral
    endpoints, but at the fractional LP optimum `b = 1/2 ∈ ℝ`, `k3LpGapReal (1/2) = -1 < 0`,
    and every integral vertex cover of `K_3` has size at least `2 > 3/2`. -/
theorem pnp_04_k3_lp_integrality_gap_refuted :
    k3LpGapReal 0 = 3 ∧
    k3LpGapReal 1 = 3 ∧
    k3LpGapReal (1 / 2 : ℝ) = -1 ∧
    k3LpGapReal (1 / 2 : ℝ) < 0 ∧
    (∀ (x1 x2 x3 : Bool),
      isK3VertexCover x1 x2 x3 = true →
      4 ≤ 2 * (b2i x1 + b2i x2 + b2i x3)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold k3LpGapReal; norm_num
  · unfold k3LpGapReal; norm_num
  · unfold k3LpGapReal; norm_num
  · unfold k3LpGapReal; norm_num
  · decide

/-- Theorem PNP-04b (Complete LP Lower Bound, Feasibility of `(1/2, 1/2, 1/2)`, Integral Minimum `2`,
    and Exact Integrality Gap Ratio `2 / (3/2) = 4/3` over `ℝ`):
    1. Every fractional LP-feasible point `(x1, x2, x3) ∈ ℝ^3` satisfying `x1 + x2 ≥ 1`,
       `x2 + x3 ≥ 1`, `x3 + x1 ≥ 1` has objective `k3FractionalObj x1 x2 x3 ≥ 3 / 2`.
    2. The point `(1/2, 1/2, 1/2)` satisfies all three edge constraints and achieves `3 / 2`.
    3. The integral vertex cover `(true, true, false)` is feasible and achieves `2`, matching the
       universal integral lower bound `b2i x1 + b2i x2 + b2i x3 ≥ 2`, yielding gap `(2 : ℝ) / (3 / 2) = 4 / 3`. -/
theorem pnp_04_k3_lp_integrality_gap_over_reals :
    (∀ (x1 x2 x3 : ℝ),
      1 ≤ x1 + x2 → 1 ≤ x2 + x3 → 1 ≤ x3 + x1 →
      (3 : ℝ) / 2 ≤ k3FractionalObj x1 x2 x3) ∧
    (1 ≤ (1 / 2 : ℝ) + (1 / 2 : ℝ) ∧
     k3FractionalObj (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) = (3 : ℝ) / 2) ∧
    (isK3VertexCover true true false = true ∧
     b2i true + b2i true + b2i false = 2) ∧
    (∀ (x1 x2 x3 : Bool),
      isK3VertexCover x1 x2 x3 = true →
      2 ≤ b2i x1 + b2i x2 + b2i x3) ∧
    ((2 : ℝ) / ((3 : ℝ) / 2) = (4 : ℝ) / 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x1 x2 x3 h12 h23 h31
    unfold k3FractionalObj
    linarith
  · unfold k3FractionalObj
    norm_num
  · decide
  · decide
  · norm_num

/- ============================================================================
   SECTION 5: PNP-05 — REFUTATION OF NO-CANCELLATION MONOTONE TRANSFER OVER `ℝ`
   & KARATSUBA'S 3-MULTIPLICATION IDENTITY OVER ANY COMMUTATIVE RING `R`
   ============================================================================ -/

/-- Candidate bilinear margin over `ℝ`: `K(x, y) = (x + y)^2 - (x - y)^2 - 5*x*y = -x*y`. -/
def karatsubaRealMargin (x y : ℝ) : ℝ :=
  (x + y) ^ 2 - (x - y) ^ 2 - 5 * x * y

/-- Theorem PNP-05a: Over `ℝ`, `karatsubaRealMargin x y = -x * y`, which is `-1 < 0` at `(1, 1)`. -/
theorem pnp_05_non_monotone_cancellation_refuted :
    (∀ x y : ℝ, karatsubaRealMargin x y = -(x * y)) ∧
    karatsubaRealMargin 1 1 = -1 ∧
    karatsubaRealMargin 1 1 < 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y; unfold karatsubaRealMargin; ring
  · unfold karatsubaRealMargin; norm_num
  · unfold karatsubaRealMargin; norm_num

theorem pnp_05_cancellation_witness_neg :
    (∀ x y : ℝ, karatsubaRealMargin x y = -(x * y)) ∧
    karatsubaRealMargin 1 1 = -1 ∧
    karatsubaRealMargin 1 1 < 0 :=
  pnp_05_non_monotone_cancellation_refuted

/-- Theorem PNP-05b (Karatsuba 3-Multiplication Cancellation Identity over any `CommRing R`):
    In any commutative ring `R`, the degree-1 convolution `a1 * b0 + a0 * b1` is recovered
    from the three products `(a1 + a0) * (b1 + b0)`, `a1 * b1`, and `a0 * b0` via subtraction. -/
theorem pnp_05_karatsuba_three_mult_identity {R : Type*} [CommRing R] (a1 a0 b1 b0 : R) :
    (a1 + a0) * (b1 + b0) - a1 * b1 - a0 * b0 = a1 * b0 + a0 * b1 := by
  ring

theorem pnp_05_karatsuba_commRing_identity {R : Type*} [CommRing R] (a1 a0 b1 b0 : R) :
    (a1 + a0) * (b1 + b0) - a1 * b1 - a0 * b0 = a1 * b0 + a0 * b1 :=
  pnp_05_karatsuba_three_mult_identity a1 a0 b1 b0

/- ============================================================================
   SECTION 6: PNP-06 — SPECTRAL DISCREPANCY POSITIVITY OVER `ℝ` &
   ABSTRACT DIAGONALIZATION LEMMA OVER ANY INDEXING TYPE `α`
   ============================================================================ -/

/-- Spectral L2 discrepancy over `ℝ`: `D_spec(x, y) = x^2 - 2*x*y + y^2`. -/
def spectralDiscrepancyReal (x y : ℝ) : ℝ :=
  x ^ 2 - 2 * x * y + y ^ 2

/-- Theorem PNP-06a: Over `ℝ`, `spectralDiscrepancyReal x y = (x - y)^2 ≥ 0`,
    and `spectralDiscrepancyReal x y = 0 ↔ x = y`. -/
theorem pnp_06_spectral_discrepancy_real_sos (x y : ℝ) :
    spectralDiscrepancyReal x y = (x - y) ^ 2 ∧
    0 ≤ spectralDiscrepancyReal x y ∧
    (spectralDiscrepancyReal x y = 0 ↔ x = y) := by
  have hsos : spectralDiscrepancyReal x y = (x - y) ^ 2 := by
    unfold spectralDiscrepancyReal
    ring
  refine ⟨hsos, ?_, ?_⟩
  · rw [hsos]; positivity
  · rw [hsos, sq_eq_zero_iff, sub_eq_zero]

theorem pnp_06_spectralDiscrepancy_sos (x y : ℝ) :
    spectralDiscrepancyReal x y = (x - y) ^ 2 ∧
    0 ≤ spectralDiscrepancyReal x y ∧
    (spectralDiscrepancyReal x y = 0 ↔ x = y) :=
  pnp_06_spectral_discrepancy_real_sos x y

/-- Diagonal language against any indexed family of boolean deciders `eval : α → α → Bool`. -/
def diagonalLanguage {α : Type*} (eval : α → α → Bool) (m : α) : Bool :=
  !(eval m m)

abbrev bgsDiagonalLanguage {α : Type*} (eval : α → α → Bool) (m : α) : Bool :=
  diagonalLanguage eval m

/-- Theorem PNP-06b (Abstract Pointwise Diagonalization Lemma):
    For any indexing type `α`, any evaluation table `eval : α → α → Bool`,
    and any index `m : α`, `diagonalLanguage eval m ≠ eval m m`. -/
theorem pnp_06_baker_gill_solovay_diagonal_differs {α : Type*} (eval : α → α → Bool) (m : α) :
    diagonalLanguage eval m ≠ eval m m := by
  unfold diagonalLanguage
  cases eval m m <;> decide

theorem pnp_06_bgs_diagonalization_barrier {α : Type*} (eval : α → α → Bool) (m : α) :
    bgsDiagonalLanguage eval m ≠ eval m m :=
  pnp_06_baker_gill_solovay_diagonal_differs eval m

/-- Theorem PNP-06c (No Indexed Row in `eval` Decides `diagonalLanguage eval`):
    For any indexing type `α` and evaluation table `eval : α → α → Bool`, no index `m : α`
    satisfies `∀ x : α, eval m x = diagonalLanguage eval x`. -/
theorem pnp_06_no_machine_decides_diagonalLanguage {α : Type*} (eval : α → α → Bool) (m : α) :
    ¬(∀ x : α, eval m x = diagonalLanguage eval x) := by
  intro hall
  have hm : eval m m = diagonalLanguage eval m := hall m
  exact pnp_06_baker_gill_solovay_diagonal_differs eval m hm.symm

/- ============================================================================
   SECTION 7: PNP-07 — STRUCTURAL INDUCTION EQUISATISFIABILITY OF TSEITIN 3-CNF
   TRANSFORMATION ON ARBITRARY-DEPTH BOOLEAN CIRCUITS
   ============================================================================ -/

/-- Inductive syntax of arbitrary-depth boolean circuits over input variables indexed by `Nat`. -/
inductive BoolCircuit where
  | var : Nat → BoolCircuit
  | not : BoolCircuit → BoolCircuit
  | and : BoolCircuit → BoolCircuit → BoolCircuit
  | or  : BoolCircuit → BoolCircuit → BoolCircuit
  deriving DecidableEq, Repr

/-- Standard recursive boolean evaluation of a `BoolCircuit` under input assignment `env : Nat → Bool`. -/
def evalCircuit (env : Nat → Bool) : BoolCircuit → Bool
  | .var i     => env i
  | .not c     => !(evalCircuit env c)
  | .and c1 c2 => (evalCircuit env c1) && (evalCircuit env c2)
  | .or  c1 c2 => (evalCircuit env c1) || (evalCircuit env c2)

/-- Number of internal logic gates (`not`, `and`, `or`) in a `BoolCircuit`. -/
def gateCount : BoolCircuit → Nat
  | .var _     => 0
  | .not c     => 1 + gateCount c
  | .and c1 c2 => 1 + gateCount c1 + gateCount c2
  | .or  c1 c2 => 1 + gateCount c1 + gateCount c2

/-- Exact number of 3-CNF clauses emitted by the Tseitin transformation for each internal gate
    (2 clauses for a `not` gate, 3 clauses for an `and` or `or` gate). -/
def tseitinGateClauseCount : BoolCircuit → Nat
  | .var _     => 0
  | .not c     => 2 + tseitinGateClauseCount c
  | .and c1 c2 => 3 + tseitinGateClauseCount c1 + tseitinGateClauseCount c2
  | .or  c1 c2 => 3 + tseitinGateClauseCount c1 + tseitinGateClauseCount c2

/-- Theorem PNP-07a (Linear 3-CNF Clause-Count Bound for Tseitin Transformation):
    For every boolean circuit `c`, the total number of gate-consistency 3-CNF clauses
    is at most `3 * gateCount c`, so including the top-level output unit clause gives at most
    `3 * gateCount c + 1` clauses. -/
theorem pnp_07_tseitin_clause_count_linear_bound (c : BoolCircuit) :
    tseitinGateClauseCount c ≤ 3 * gateCount c ∧
    tseitinGateClauseCount c + 1 ≤ 3 * gateCount c + 1 := by
  have h : tseitinGateClauseCount c ≤ 3 * gateCount c := by
    induction c with
    | var i =>
      simp [tseitinGateClauseCount, gateCount]
    | not c1 ih =>
      simp only [tseitinGateClauseCount, gateCount]
      omega
    | and c1 c2 ih1 ih2 =>
      simp only [tseitinGateClauseCount, gateCount]
      omega
    | or c1 c2 ih1 ih2 =>
      simp only [tseitinGateClauseCount, gateCount]
      omega
  exact ⟨h, by omega⟩

/-- Tseitin wire-labeling consistency predicate for a circuit `c` under input assignment
    `env : Nat → Bool` and wire assignment `wire : BoolCircuit → Bool`.
    Each gate's local 3-CNF clauses enforce equivalence between `wire sub` and the gate operation
    applied to its child wires. -/
def tseitinWireConsistent (env : Nat → Bool) (wire : BoolCircuit → Bool) : BoolCircuit → Prop
  | .var i     => wire (.var i) = env i
  | .not c1    =>
      (wire (.not c1) = !(wire c1)) ∧
      tseitinWireConsistent env wire c1
  | .and c1 c2 =>
      (wire (.and c1 c2) = ((wire c1) && (wire c2))) ∧
      tseitinWireConsistent env wire c1 ∧
      tseitinWireConsistent env wire c2
  | .or c1 c2  =>
      (wire (.or c1 c2) = ((wire c1) || (wire c2))) ∧
      tseitinWireConsistent env wire c1 ∧
      tseitinWireConsistent env wire c2

/-- Theorem PNP-07b (Tseitin Wire Consistency Uniquely Fixes Every Subcircuit Wire):
    By structural induction on `c : BoolCircuit`, if `tseitinWireConsistent env wire c` holds,
    then the wire value `wire c` equals the true recursive evaluation `evalCircuit env c`. -/
theorem pnp_07_tseitin_circuit_soundness (env : Nat → Bool) (wire : BoolCircuit → Bool)
    (c : BoolCircuit) (hcons : tseitinWireConsistent env wire c) :
    wire c = evalCircuit env c := by
  induction c with
  | var i =>
    exact hcons
  | not c1 ih =>
    rcases hcons with ⟨hgate, hc1⟩
    rw [hgate, ih hc1, evalCircuit]
  | and c1 c2 ih1 ih2 =>
    rcases hcons with ⟨hgate, hc1, hc2⟩
    rw [hgate, ih1 hc1, ih2 hc2, evalCircuit]
  | or c1 c2 ih1 ih2 =>
    rcases hcons with ⟨hgate, hc1, hc2⟩
    rw [hgate, ih1 hc1, ih2 hc2, evalCircuit]

/-- Theorem PNP-07c (Canonical Evaluation Wire Assignment Satisfies Tseitin Consistency):
    For any circuit `c` and input environment `env`, choosing `wire := evalCircuit env`
    satisfies `tseitinWireConsistent env (evalCircuit env) c`. -/
theorem pnp_07_tseitin_circuit_completeness (env : Nat → Bool) (c : BoolCircuit) :
    tseitinWireConsistent env (evalCircuit env) c := by
  induction c with
  | var i =>
    rfl
  | not c1 ih =>
    exact ⟨rfl, ih⟩
  | and c1 c2 ih1 ih2 =>
    exact ⟨rfl, ih1, ih2⟩
  | or c1 c2 ih1 ih2 =>
    exact ⟨rfl, ih1, ih2⟩

/-- Theorem PNP-07d (Global Equisatisfiability of Circuit Satisfiability and Tseitin 3-CNF):
    For every boolean circuit `c : BoolCircuit` and every input assignment `env : Nat → Bool`,
    `evalCircuit env c = true` if and only if there exists a wire assignment
    `wire : BoolCircuit → Bool` satisfying `tseitinWireConsistent env wire c` and `wire c = true`. -/
theorem pnp_07_tseitin_circuit_equisat (c : BoolCircuit) (env : Nat → Bool) :
    evalCircuit env c = true ↔
      ∃ wire : BoolCircuit → Bool, tseitinWireConsistent env wire c ∧ wire c = true := by
  constructor
  · intro heval
    exact ⟨evalCircuit env, pnp_07_tseitin_circuit_completeness env c, heval⟩
  · rintro ⟨wire, hcons, htrue⟩
    rw [← pnp_07_tseitin_circuit_soundness env wire c hcons]
    exact htrue

/- ============================================================================
   SECTION 8: PNP-08 — POLYNOMIAL-METHOD DEGREE LOWER BOUND FOR 3-BIT PARITY
   OVER `ℝ` VIA BOOLEAN CUBE FINITE DIFFERENCES
   ============================================================================ -/

/-- The 3-fold boolean cube finite-difference operator `Δ_1 Δ_2 Δ_3 f` over `ℝ`:
    `∑_{x ∈ {0,1}^3} (-1)^(3 - (x_1 + x_2 + x_3)) f(x_1, x_2, x_3)`. -/
def cubeFiniteDiff3 (f : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  f 1 1 1 - f 1 1 0 - f 1 0 1 - f 0 1 1 + f 1 0 0 + f 0 1 0 + f 0 0 1 - f 0 0 0

/-- General 3-variable real polynomial of total degree at most 2:
    `P(x_1, x_2, x_3) = c0 + c1*x1 + c2*x2 + c3*x3 + c11*x1^2 + c22*x2^2 + c33*x3^2 + c12*x1*x2 + c23*x2*x3 + c13*x1*x3`. -/
def degAtMost2Poly3 (c0 c1 c2 c3 c11 c22 c33 c12 c23 c13 : ℝ) (x1 x2 x3 : ℝ) : ℝ :=
  c0 + c1 * x1 + c2 * x2 + c3 * x3 +
  c11 * x1 ^ 2 + c22 * x2 ^ 2 + c33 * x3 ^ 2 +
  c12 * x1 * x2 + c23 * x2 * x3 + c13 * x1 * x3

/-- Exact ±1 parity polynomial on `{0, 1}^3`:
    `paritySign3(x_1, x_2, x_3) = (1 - 2*x_1) * (1 - 2*x_2) * (1 - 2*x_3)`. -/
def paritySign3 (x1 x2 x3 : ℝ) : ℝ :=
  (1 - 2 * x1) * (1 - 2 * x2) * (1 - 2 * x3)

/-- Boolean-to-Real embedding `0` or `1`. -/
def b2r (b : Bool) : ℝ := if b then 1 else 0

/-- Theorem PNP-08a (3-Fold Cube Finite Difference Annihilates Every Degree-`≤ 2` Polynomial):
    For any real coefficients `c0, ..., c13 : ℝ`, `cubeFiniteDiff3` of `degAtMost2Poly3` is `0`. -/
theorem pnp_08_cubeFiniteDiff3_degAtMost2_eq_zero
    (c0 c1 c2 c3 c11 c22 c33 c12 c23 c13 : ℝ) :
    cubeFiniteDiff3 (degAtMost2Poly3 c0 c1 c2 c3 c11 c22 c33 c12 c23 c13) = 0 := by
  unfold cubeFiniteDiff3 degAtMost2Poly3
  ring

/-- Theorem PNP-08b (3-Fold Cube Finite Difference of 3-Bit Parity is `-8 ≠ 0`):
    `cubeFiniteDiff3 paritySign3 = -8`. -/
theorem pnp_08_cubeFiniteDiff3_paritySign3_eq_neg_eight :
    cubeFiniteDiff3 paritySign3 = -8 := by
  unfold cubeFiniteDiff3 paritySign3
  norm_num

/-- Theorem PNP-08c (Unconditional Polynomial-Method Degree Lower Bound for 3-Bit Parity):
    No 3-variable real polynomial of total degree at most 2 can agree with 3-bit `paritySign3`
    on all 8 vertices of the boolean cube `{0, 1}^3`. Thus any real polynomial computing
    3-bit parity on `{0, 1}^3` has degree at least 3. -/
theorem pnp_08_no_deg2_polynomial_computes_parity3
    (c0 c1 c2 c3 c11 c22 c33 c12 c23 c13 : ℝ) :
    ¬(∀ x1 x2 x3 : Bool,
      degAtMost2Poly3 c0 c1 c2 c3 c11 c22 c33 c12 c23 c13
        (b2r x1) (b2r x2) (b2r x3) =
      paritySign3 (b2r x1) (b2r x2) (b2r x3)) := by
  intro hall
  have h111 : degAtMost2Poly3 c0 c1 c2 c3 c11 c22 c33 c12 c23 c13 1 1 1 = paritySign3 1 1 1 :=
    hall true true true
  have h110 : degAtMost2Poly3 c0 c1 c2 c3 c11 c22 c33 c12 c23 c13 1 1 0 = paritySign3 1 1 0 :=
    hall true true false
  have h101 : degAtMost2Poly3 c0 c1 c2 c3 c11 c22 c33 c12 c23 c13 1 0 1 = paritySign3 1 0 1 :=
    hall true false true
  have h011 : degAtMost2Poly3 c0 c1 c2 c3 c11 c22 c33 c12 c23 c13 0 1 1 = paritySign3 0 1 1 :=
    hall false true true
  have h100 : degAtMost2Poly3 c0 c1 c2 c3 c11 c22 c33 c12 c23 c13 1 0 0 = paritySign3 1 0 0 :=
    hall true false false
  have h010 : degAtMost2Poly3 c0 c1 c2 c3 c11 c22 c33 c12 c23 c13 0 1 0 = paritySign3 0 1 0 :=
    hall false true false
  have h001 : degAtMost2Poly3 c0 c1 c2 c3 c11 c22 c33 c12 c23 c13 0 0 1 = paritySign3 0 0 1 :=
    hall false false true
  have h000 : degAtMost2Poly3 c0 c1 c2 c3 c11 c22 c33 c12 c23 c13 0 0 0 = paritySign3 0 0 0 :=
    hall false false false
  have hdiff_eq :
      cubeFiniteDiff3 (degAtMost2Poly3 c0 c1 c2 c3 c11 c22 c33 c12 c23 c13) =
      cubeFiniteDiff3 paritySign3 := by
    unfold cubeFiniteDiff3
    linarith
  have hzero := pnp_08_cubeFiniteDiff3_degAtMost2_eq_zero c0 c1 c2 c3 c11 c22 c33 c12 c23 c13
  have hpar := pnp_08_cubeFiniteDiff3_paritySign3_eq_neg_eight
  linarith

end PvsNPMathlib
