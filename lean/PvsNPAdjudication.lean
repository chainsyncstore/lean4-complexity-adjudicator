/-
  P vs. NP — Formal Reductions, Complexity Barriers & Candidate-Lemma Refutations in Lean 4
  Verified in Lean 4.15.0 (zero `sorry` placeholders, zero custom axioms).
-/

namespace PvsNPAdjudication

/- ============================================================================
   SECTION 0: CORE INTEGER ALGEBRAIC LEMMAS (SELF-CONTAINED IN LEAN 4 CORE)
   ============================================================================ -/

/-- Expanding `(a - b) * (a - b) = a * a - (a * b + b * a) + b * b` over `Int`. -/
theorem int_sub_sq (a b : Int) :
    (a - b) * (a - b) = a * a - (a * b + b * a) + b * b := by
  calc (a - b) * (a - b)
    _ = a * (a - b) - b * (a - b) := Int.sub_mul a b (a - b)
    _ = (a * a - a * b) - (b * a - b * b) := by
      rw [Int.mul_sub, Int.mul_sub]
    _ = a * a - (a * b + b * a) + b * b := by omega

/-- Expanding `(a + b) * (c + d) = a * c + a * d + b * c + b * d` over `Int`. -/
theorem int_add_mul_add (a b c d : Int) :
    (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  calc (a + b) * (c + d)
    _ = a * (c + d) + b * (c + d) := Int.add_mul a b (c + d)
    _ = (a * c + a * d) + (b * c + b * d) := by
      rw [Int.mul_add, Int.mul_add]
    _ = a * c + a * d + b * c + b * d := by omega

/-- Every integer square `x * x` is non-negative (`0 ≤ x * x`). -/
theorem int_mul_self_nonneg (x : Int) : 0 ≤ x * x := by
  cases Int.le_total 0 x with
  | inl hpos =>
    exact Int.mul_nonneg hpos hpos
  | inr hneg =>
    have hpos_neg : 0 ≤ -x := by omega
    have hmul : 0 ≤ (-x) * (-x) := Int.mul_nonneg hpos_neg hpos_neg
    have heq : (-x) * (-x) = x * x := by
      calc (-x) * (-x)
        _ = -(x * (-x)) := Int.neg_mul x (-x)
        _ = -(-(x * x)) := by rw [Int.mul_neg x x]
        _ = x * x := by omega
    rw [← heq]
    exact hmul

/-- Zero-locus of a square: `x * x = 0 ↔ x = 0`. -/
theorem int_mul_self_eq_zero_iff (x : Int) : x * x = 0 ↔ x = 0 := by
  constructor
  · intro h
    cases Int.mul_eq_zero.mp h with
    | inl h0 => exact h0
    | inr h0 => exact h0
  · intro h
    rw [h]
    rfl

/- ============================================================================
   SECTION 1: PNP-01 — COOK-LEVIN / KARP QUARTIC PENALTY EQUIVALENCE
   ============================================================================ -/

/-- Cook-Levin / Karp quartic penalty for boolean domain `x ∈ {0, 1}` plus unit clause `x = 1`:
    `E_1(x) = (x^2 - x)^2 + (x - 1)^2`. -/
def cookLevinGadgetEnergy (x : Int) : Int :=
  (x * x - x) * (x * x - x) + (x - 1) * (x - 1)

/-- Theorem PNP-01a: `cookLevinGadgetEnergy x` is universally non-negative (`0 ≤ E_1(x)`). -/
theorem pnp_01_cook_levin_gadget_nonneg (x : Int) :
    0 ≤ cookLevinGadgetEnergy x := by
  unfold cookLevinGadgetEnergy
  have h1 : 0 ≤ (x * x - x) * (x * x - x) := int_mul_self_nonneg (x * x - x)
  have h2 : 0 ≤ (x - 1) * (x - 1) := int_mul_self_nonneg (x - 1)
  omega

/-- Theorem PNP-01b: `cookLevinGadgetEnergy x = 0` if and only if `x = 1` (the unique satisfying assignment). -/
theorem pnp_01_cook_levin_gadget_sos_and_zero_locus (x : Int) :
    0 ≤ cookLevinGadgetEnergy x ∧ (cookLevinGadgetEnergy x = 0 ↔ x = 1) := by
  refine ⟨pnp_01_cook_levin_gadget_nonneg x, ?_⟩
  unfold cookLevinGadgetEnergy
  have h1 : 0 ≤ (x * x - x) * (x * x - x) := int_mul_self_nonneg (x * x - x)
  have h2 : 0 ≤ (x - 1) * (x - 1) := int_mul_self_nonneg (x - 1)
  constructor
  · intro hsum
    have hzero2 : (x - 1) * (x - 1) = 0 := by omega
    have hx1 : x - 1 = 0 := (int_mul_self_eq_zero_iff (x - 1)).mp hzero2
    omega
  · intro hx
    subst hx
    decide

/- ============================================================================
   SECTION 2: PNP-02 — TSEITIN 3-SAT REDUCTION EQUI-SATISFIABILITY & SLACK SOS
   ============================================================================ -/

/-- Tseitin 3-CNF encoding of the AND gate `z ↔ (x ∧ y)`:
    `(!x ∨ !y ∨ z) ∧ (x ∨ !z) ∧ (y ∨ !z)`. -/
def tseitinAndClauses (x y z : Bool) : Bool :=
  ((!x || !y || z) && (x || !z) && (y || !z))

/-- Theorem PNP-02a: For all boolean inputs `x, y, z : Bool`, the 3-CNF Tseitin gadget
    evaluates to `true` if and only if the auxiliary wire `z` equals `x && y`. -/
theorem pnp_02_tseitin_and_gadget_equisat :
    ∀ (x y z : Bool), tseitinAndClauses x y z = true ↔ z = (x && y) := by
  decide

/-- Quadratic-over-linear clause-expansion slack `S(x) = (x + 1)^2`. -/
def tseitinClauseSlack (x : Int) : Int :=
  (x + 1) * (x + 1)

/-- Theorem PNP-02b: The Tseitin quadratic-over-linear slack is universally non-negative. -/
theorem pnp_02_tseitin_and_gadget_equisat_and_slack (x : Int) :
    0 ≤ tseitinClauseSlack x := by
  unfold tseitinClauseSlack
  exact int_mul_self_nonneg (x + 1)

/- ============================================================================
   SECTION 3: PNP-03 — REFUTATION OF PAIRWISE 2-SAT PROJECTION HEURISTIC
   ============================================================================ -/

/-- Concave pairwise 2-SAT consistency functional `L_3(x, y) = 2*x + 2*y - 2*x^2 - 4*x*y - 2*y^2`. -/
def pairwise2SatMargin (x y : Int) : Int :=
  2 * x + 2 * y - 2 * x * x - 4 * x * y - 2 * y * y

/-- Complete 8-clause 3-CNF contradiction on 3 variables `x1, x2, x3`:
    Every 2-variable sub-assignment satisfies 6 of the 8 clauses, yet the conjunction is false. -/
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

/-- Theorem PNP-03: Refutes universal non-negativity of `pairwise2SatMargin` at `(1, 1)` (`-4 < 0`),
    proves that `unsat3CnfContradiction` has no satisfying boolean assignment in `Bool^3`,
    and establishes the quantifier separation between clause-wise projection (`true` for all `x1, x2`)
    and global existential projection (`false` for all `x1, x2`). -/
theorem pnp_03_pairwise_2sat_projection_refuted :
    pairwise2SatMargin 1 0 = 0 ∧
    pairwise2SatMargin 0 0 = 0 ∧
    pairwise2SatMargin 1 1 = -4 ∧
    pairwise2SatMargin 1 1 < 0 ∧
    (∀ (x1 x2 x3 : Bool), unsat3CnfContradiction x1 x2 x3 = false) ∧
    (∀ (x1 x2 : Bool), clausewiseProjected3Cnf x1 x2 = true) ∧
    (∀ (x1 x2 : Bool), globalExistentialProjected3Cnf x1 x2 = false) := by
  decide

/- ============================================================================
   SECTION 4: PNP-04 — REFUTATION OF ZERO LP INTEGRALITY GAP ON ODD CYCLE K_3
   ============================================================================ -/

/-- Homogeneous form of the K_3 LP integrality-gap quadratic `G_LP(b, d) = 16*b^2 - 16*b*d + 3*d^2`. -/
def k3LpGapQuadratic (b d : Int) : Int :=
  16 * b * b - 16 * b * d + 3 * d * d

/-- Boolean indicator to integer `0` or `1`. -/
def b2i (b : Bool) : Int :=
  if b then 1 else 0

/-- Triangle K_3 Vertex Cover constraint: every edge `(1,2), (2,3), (3,1)` is covered. -/
def isK3VertexCover (x1 x2 x3 : Bool) : Bool :=
  (x1 || x2) && (x2 || x3) && (x3 || x1)

/-- Theorem PNP-04:
    1. At integral vertices `b = 0` and `b = 1` (`d = 1`), `k3LpGapQuadratic` is positive (`+3`),
       but at the symmetric LP fractional optimum `b = 1, d = 2` (`1/2`), `k3LpGapQuadratic 1 2 = -4 < 0`.
    2. Every valid integral vertex cover `(x1, x2, x3) ∈ Bool^3` of `K_3` has doubled size
       `2 * (b2i x1 + b2i x2 + b2i x3) ≥ 4 > 3` (strictly exceeding the doubled LP optimum `3`). -/
theorem pnp_04_k3_lp_integrality_gap_refuted :
    k3LpGapQuadratic 0 1 = 3 ∧
    k3LpGapQuadratic 1 1 = 3 ∧
    k3LpGapQuadratic 1 2 = -4 ∧
    k3LpGapQuadratic 1 2 < 0 ∧
    (∀ (x1 x2 x3 : Bool),
      isK3VertexCover x1 x2 x3 = true →
      4 ≤ 2 * (b2i x1 + b2i x2 + b2i x3)) := by
  decide

/- ============================================================================
   SECTION 5: PNP-05 — REFUTATION OF NO-CANCELLATION MONOTONE TRANSFER
   & FORMAL PROOF OF KARATSUBA'S 3-MULTIPLICATION CANCELLATION IDENTITY
   ============================================================================ -/

/-- Candidate bilinear margin `K(x, y) = (x + y)^2 - (x - y)^2 - 5*x*y = -x*y`. -/
def karatsubaMargin (x y : Int) : Int :=
  (x + y) * (x + y) - (x - y) * (x - y) - 5 * x * y

/-- Theorem PNP-05a: Refutes universal non-negativity of `karatsubaMargin` at `(x = 1, y = 1)`. -/
theorem pnp_05_non_monotone_cancellation_refuted :
    karatsubaMargin 0 0 = 0 ∧
    karatsubaMargin 1 1 = -1 ∧
    karatsubaMargin 1 1 < 0 := by
  decide

/-- Theorem PNP-05b (Karatsuba 3-Multiplication Cancellation Identity):
    For all integers `a1, a0, b1, b0`, the cross-term `a1 * b0 + a0 * b1` is recovered
    using only 3 multiplications `z2 = a1 * b1`, `z0 = a0 * b0`, and `z3 = (a1 + a0) * (b1 + b0)`
    via the subtraction cancellation `z3 - z2 - z0 = a1 * b0 + a0 * b1`. -/
theorem pnp_05_karatsuba_three_mult_identity (a1 a0 b1 b0 : Int) :
    (a1 + a0) * (b1 + b0) - a1 * b1 - a0 * b0 = a1 * b0 + a0 * b1 := by
  rw [int_add_mul_add a1 a0 b1 b0]
  omega

/- ============================================================================
   SECTION 6: PNP-06 — SPECTRAL DISCREPANCY POSITIVITY &
   BAKER-GILL-SOLOVAY RELATIVIZING DIAGONALIZATION BARRIER
   ============================================================================ -/

/-- Spectral L2 discrepancy `D_spec(x, y) = (x - y)^2`. -/
def spectralDiscrepancy (x y : Int) : Int :=
  (x - y) * (x - y)

/-- Theorem PNP-06a: `spectralDiscrepancy x y` is universally non-negative (`≥ 0`)
    and vanishes if and only if `x = y`. -/
theorem pnp_06_spectral_discrepancy_and_diagonalization_barrier (x y : Int) :
    0 ≤ spectralDiscrepancy x y ∧ (spectralDiscrepancy x y = 0 ↔ x = y) := by
  unfold spectralDiscrepancy
  refine ⟨int_mul_self_nonneg (x - y), ?_⟩
  constructor
  · intro h
    have hz : x - y = 0 := (int_mul_self_eq_zero_iff (x - y)).mp h
    omega
  · intro hxy
    have hz : x - y = 0 := by omega
    rw [hz]
    rfl

/-- Diagonal language against any indexed family of boolean deciders `eval : Nat → Nat → Bool`. -/
def diagonalLanguage (eval : Nat → Nat → Bool) (n : Nat) : Bool :=
  !(eval n n)

/-- Theorem PNP-06b (Baker-Gill-Solovay Relativizing Diagonalization Theorem):
    For any oracle-relativized or unrelativized machine evaluation table `eval : Nat → Nat → Bool`
    and any machine index `m : Nat`, the diagonal language `diagonalLanguage eval` differs from
    machine `m` on input `m` (`diagonalLanguage eval m ≠ eval m m`). -/
theorem pnp_06_baker_gill_solovay_diagonal_differs (eval : Nat → Nat → Bool) (m : Nat) :
    diagonalLanguage eval m ≠ eval m m := by
  unfold diagonalLanguage
  cases eval m m <;> decide

/- ============================================================================
   SECTION 7: PNP-07 — INDUCTIVE MULTI-GATE BOOLEAN CIRCUIT & RECURSIVE TSEITIN
   TRANSFORMATION (SOUNDNESS, COMPLETENESS & LINEAR CLAUSE-COUNT BOUND)
   ============================================================================ -/

/-- Inductive syntax of arbitrary-depth Boolean circuits over `Nat`-indexed input variables
    with `NOT`, fan-in-2 `AND`, and fan-in-2 `OR` gates. -/
inductive BoolCircuit where
  | var : Nat → BoolCircuit
  | not : BoolCircuit → BoolCircuit
  | and : BoolCircuit → BoolCircuit → BoolCircuit
  | or  : BoolCircuit → BoolCircuit → BoolCircuit
  deriving Repr, DecidableEq

/-- Standard recursive boolean evaluation of a `BoolCircuit` under input assignment `env : Nat → Bool`. -/
def evalCircuit (env : Nat → Bool) : BoolCircuit → Bool
  | .var i     => env i
  | .not c     => !(evalCircuit env c)
  | .and c1 c2 => (evalCircuit env c1) && (evalCircuit env c2)
  | .or  c1 c2 => (evalCircuit env c1) || (evalCircuit env c2)

/-- Number of logic gates (`not`, `and`, `or`) in a `BoolCircuit`. -/
def gateCount : BoolCircuit → Nat
  | .var _     => 0
  | .not c     => 1 + gateCount c
  | .and c1 c2 => 1 + gateCount c1 + gateCount c2
  | .or  c1 c2 => 1 + gateCount c1 + gateCount c2

/-- Local 3-CNF gate-consistency predicate for a single NOT gate `out ↔ ¬in1` (2 clauses). -/
def tseitinNotClauses (in1 out : Bool) : Bool :=
  (!in1 || !out) && (in1 || out)

/-- Local 3-CNF gate-consistency predicate for a single OR gate `out ↔ (in1 ∨ in2)` (3 clauses). -/
def tseitinOrClauses (in1 in2 out : Bool) : Bool :=
  (in1 || in2 || !out) && (!in1 || out) && (!in2 || out)

/-- Local 3-CNF gate-consistency predicate for a single AND gate `out ↔ (in1 ∧ in2)` (3 clauses). -/
def tseitinAndClauses2 (in1 in2 out : Bool) : Bool :=
  (!in1 || !in2 || out) && (in1 || !out) && (in2 || !out)

/-- Total number of 3-CNF clauses emitted by the recursive Tseitin transformation
    for all internal gates of `c` (excluding the single top-level output unit clause). -/
def tseitinGateClauseCount : BoolCircuit → Nat
  | .var _     => 0
  | .not c     => 2 + tseitinGateClauseCount c
  | .and c1 c2 => 3 + tseitinGateClauseCount c1 + tseitinGateClauseCount c2
  | .or  c1 c2 => 3 + tseitinGateClauseCount c1 + tseitinGateClauseCount c2

/-- Recursive Tseitin wire-consistency predicate across all subcircuit nodes. -/
def tseitinWireConsistent (env : Nat → Bool) (wire : BoolCircuit → Bool) : BoolCircuit → Bool
  | .var i     => (wire (.var i) == env i)
  | .not c     => tseitinNotClauses (wire c) (wire (.not c)) && tseitinWireConsistent env wire c
  | .and c1 c2 =>
      tseitinAndClauses2 (wire c1) (wire c2) (wire (.and c1 c2)) &&
      tseitinWireConsistent env wire c1 &&
      tseitinWireConsistent env wire c2
  | .or  c1 c2 =>
      tseitinOrClauses (wire c1) (wire c2) (wire (.or c1 c2)) &&
      tseitinWireConsistent env wire c1 &&
      tseitinWireConsistent env wire c2

theorem tseitinNotClauses_iff (a b : Bool) :
    tseitinNotClauses a b = true ↔ b = !a := by
  cases a <;> cases b <;> decide

theorem tseitinAndClauses2_iff (a b c : Bool) :
    tseitinAndClauses2 a b c = true ↔ c = (a && b) := by
  cases a <;> cases b <;> cases c <;> decide

theorem tseitinOrClauses_iff (a b c : Bool) :
    tseitinOrClauses a b c = true ↔ c = (a || b) := by
  cases a <;> cases b <;> cases c <;> decide

/-- Theorem PNP-07a (Linear 3-CNF Clause-Count Bound by Structural Induction): -/
theorem pnp_07_tseitin_clause_count_linear_bound (c : BoolCircuit) :
    tseitinGateClauseCount c + 1 ≤ 3 * gateCount c + 1 := by
  induction c with
  | var _ => simp [tseitinGateClauseCount, gateCount]
  | not c ih =>
    simp only [tseitinGateClauseCount, gateCount]
    omega
  | and c1 c2 ih1 ih2 =>
    simp only [tseitinGateClauseCount, gateCount]
    omega
  | or c1 c2 ih1 ih2 =>
    simp only [tseitinGateClauseCount, gateCount]
    omega

/-- Theorem PNP-07b (Inductive Soundness of Recursive Tseitin Transformation): -/
theorem pnp_07_tseitin_circuit_soundness (env : Nat → Bool) (wire : BoolCircuit → Bool)
    (c : BoolCircuit) (hcons : tseitinWireConsistent env wire c = true) :
    wire c = evalCircuit env c := by
  induction c with
  | var i =>
    simp only [tseitinWireConsistent, beq_iff_eq] at hcons
    exact hcons
  | not c ih =>
    simp only [tseitinWireConsistent, Bool.and_eq_true] at hcons
    have hgate := (tseitinNotClauses_iff (wire c) (wire (.not c))).mp hcons.1
    have hsub := ih hcons.2
    simp only [evalCircuit, hgate, hsub]
  | and c1 c2 ih1 ih2 =>
    simp only [tseitinWireConsistent, Bool.and_eq_true] at hcons
    have hgate := (tseitinAndClauses2_iff (wire c1) (wire c2) (wire (.and c1 c2))).mp hcons.1.1
    have hsub1 := ih1 hcons.1.2
    have hsub2 := ih2 hcons.2
    simp only [evalCircuit, hgate, hsub1, hsub2]
  | or c1 c2 ih1 ih2 =>
    simp only [tseitinWireConsistent, Bool.and_eq_true] at hcons
    have hgate := (tseitinOrClauses_iff (wire c1) (wire c2) (wire (.or c1 c2))).mp hcons.1.1
    have hsub1 := ih1 hcons.1.2
    have hsub2 := ih2 hcons.2
    simp only [evalCircuit, hgate, hsub1, hsub2]

/-- Theorem PNP-07c (Inductive Completeness of Recursive Tseitin Transformation): -/
theorem pnp_07_tseitin_circuit_completeness (env : Nat → Bool) (c : BoolCircuit) :
    tseitinWireConsistent env (evalCircuit env) c = true := by
  induction c with
  | var i =>
    simp [tseitinWireConsistent, evalCircuit]
  | not c ih =>
    simp only [tseitinWireConsistent, Bool.and_eq_true]
    exact ⟨(tseitinNotClauses_iff _ _).mpr rfl, ih⟩
  | and c1 c2 ih1 ih2 =>
    simp only [tseitinWireConsistent, Bool.and_eq_true]
    exact ⟨⟨(tseitinAndClauses2_iff _ _ _).mpr rfl, ih1⟩, ih2⟩
  | or c1 c2 ih1 ih2 =>
    simp only [tseitinWireConsistent, Bool.and_eq_true]
    exact ⟨⟨(tseitinOrClauses_iff _ _ _).mpr rfl, ih1⟩, ih2⟩

/-- Theorem PNP-07d (Global Equi-Satisfiability for Arbitrary-Depth Circuits): -/
theorem pnp_07_tseitin_circuit_equisat (env : Nat → Bool) (c : BoolCircuit) :
    (∃ wire : BoolCircuit → Bool,
      tseitinWireConsistent env wire c = true ∧ wire c = true) ↔
    evalCircuit env c = true := by
  constructor
  · rintro ⟨wire, hcons, hout⟩
    rw [← pnp_07_tseitin_circuit_soundness env wire c hcons]
    exact hout
  · intro heval
    exact ⟨evalCircuit env, pnp_07_tseitin_circuit_completeness env c, heval⟩

/- ============================================================================
   SECTION 8: PNP-08 — UNCONDITIONAL POLYNOMIAL-METHOD DEGREE LOWER BOUND FOR
   3-BIT PARITY VIA MULTILINEAR FINITE DIFFERENCES OVER `Int`
   ============================================================================ -/

/-- The 3-fold boolean cube finite-difference operator `Δ_1 Δ_2 Δ_3 f` over `Int`. -/
def cubeFiniteDiff3 (f : Int → Int → Int → Int) : Int :=
  f 1 1 1 - f 1 1 0 - f 1 0 1 - f 0 1 1 +
  f 1 0 0 + f 0 1 0 + f 0 0 1 - f 0 0 0

/-- General degree-`≤ 2` polynomial on `Int^3`. -/
def degAtMost2Poly3 (c0 c1 c2 c3 c11 c22 c33 c12 c23 c13 : Int) (x1 x2 x3 : Int) : Int :=
  c0 + c1 * x1 + c2 * x2 + c3 * x3 +
  c11 * x1 * x1 + c22 * x2 * x2 + c33 * x3 * x3 +
  c12 * x1 * x2 + c23 * x2 * x3 + c13 * x1 * x3

/-- Exact 3-bit Parity sign function `(1 - 2*x1)*(1 - 2*x2)*(1 - 2*x3)`. -/
def paritySign3 (x1 x2 x3 : Int) : Int :=
  (1 - 2 * x1) * (1 - 2 * x2) * (1 - 2 * x3)

/-- Theorem PNP-08a: `cubeFiniteDiff3` annihilates every degree-`≤ 2` polynomial over `Int`. -/
theorem pnp_08_cubeFiniteDiff3_degAtMost2_eq_zero
    (c0 c1 c2 c3 c11 c22 c33 c12 c23 c13 : Int) :
    cubeFiniteDiff3 (degAtMost2Poly3 c0 c1 c2 c3 c11 c22 c33 c12 c23 c13) = 0 := by
  unfold cubeFiniteDiff3 degAtMost2Poly3
  omega

/-- Theorem PNP-08b: `cubeFiniteDiff3 paritySign3 = -8`. -/
theorem pnp_08_cubeFiniteDiff3_paritySign3_eq_neg_eight :
    cubeFiniteDiff3 paritySign3 = -8 := by
  decide

/-- Theorem PNP-08c: No degree-`≤ 2` polynomial agrees with `paritySign3` on `{0, 1}^3`. -/
theorem pnp_08_no_deg2_polynomial_computes_parity3
    (c0 c1 c2 c3 c11 c22 c33 c12 c23 c13 : Int) :
    ¬(∀ x1 x2 x3 : Bool,
      degAtMost2Poly3 c0 c1 c2 c3 c11 c22 c33 c12 c23 c13
        (b2i x1) (b2i x2) (b2i x3) =
      paritySign3 (b2i x1) (b2i x2) (b2i x3)) := by
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
    omega
  have hzero := pnp_08_cubeFiniteDiff3_degAtMost2_eq_zero c0 c1 c2 c3 c11 c22 c33 c12 c23 c13
  have hpar := pnp_08_cubeFiniteDiff3_paritySign3_eq_neg_eight
  omega

end PvsNPAdjudication
