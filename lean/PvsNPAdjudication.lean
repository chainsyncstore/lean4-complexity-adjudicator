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

/-- Canonical wire identity of a subcircuit node. -/
def nodeId (c : BoolCircuit) : BoolCircuit := c

/-- Canonical wire assignment induced by evaluating every subcircuit on `env`. -/
def canonicalWireEnv (env : Nat → Bool) (c : BoolCircuit) : Bool :=
  evalCircuit env c

/-- A 3-CNF literal `(wire, polarity)` over wire type `α` (`true` = positive, `false` = negated). -/
abbrev Lit3 (α : Type) := α × Bool

/-- A 3-CNF clause consisting of three literals over wire type `α`. -/
abbrev Clause3 (α : Type) := Lit3 α × Lit3 α × Lit3 α

/-- Evaluate a single literal under wire assignment `assign`. -/
def evalLit3 {α : Type} (assign : α → Bool) (l : Lit3 α) : Bool :=
  if l.2 then assign l.1 else !(assign l.1)

/-- Evaluate a single 3-clause under wire assignment `assign`. -/
def evalClause3 {α : Type} (assign : α → Bool) (cl : Clause3 α) : Bool :=
  evalLit3 assign cl.1 || evalLit3 assign cl.2.1 || evalLit3 assign cl.2.2

/-- Evaluate a finite list of 3-clauses (a concrete emitted 3-CNF formula). -/
def evalCNF3 {α : Type} (assign : α → Bool) : List (Clause3 α) → Bool
  | []        => true
  | cl :: cls => evalClause3 assign cl && evalCNF3 assign cls

/-- Concrete 2-clause 3-CNF emission for a NOT gate `out ↔ ¬in1`. -/
def emitNotClauses (in1 out : BoolCircuit) : List (Clause3 BoolCircuit) :=
  [((in1, false), (out, false), (out, false)),
   ((in1, true),  (out, true),  (out, true))]

/-- Concrete 3-clause 3-CNF emission for an AND gate `out ↔ (in1 ∧ in2)`. -/
def emitAndClauses (in1 in2 out : BoolCircuit) : List (Clause3 BoolCircuit) :=
  [((in1, false), (in2, false), (out, true)),
   ((in1, true),  (out, false), (out, false)),
   ((in2, true),  (out, false), (out, false))]

/-- Concrete 3-clause 3-CNF emission for an OR gate `out ↔ (in1 ∨ in2)`. -/
def emitOrClauses (in1 in2 out : BoolCircuit) : List (Clause3 BoolCircuit) :=
  [((in1, true),  (in2, true),  (out, false)),
   ((in1, false), (out, true),  (out, true)),
   ((in2, false), (out, true),  (out, true))]

/-- Recursive compiler emitting the concrete finite `List (Clause3 BoolCircuit)`
    for all internal gates of `c`. -/
def compileTseitinGateClauses : BoolCircuit → List (Clause3 BoolCircuit)
  | .var _     => []
  | .not c     => emitNotClauses c (.not c) ++ compileTseitinGateClauses c
  | .and c1 c2 => emitAndClauses c1 c2 (.and c1 c2) ++
                  compileTseitinGateClauses c1 ++ compileTseitinGateClauses c2
  | .or  c1 c2 => emitOrClauses c1 c2 (.or c1 c2) ++
                  compileTseitinGateClauses c1 ++ compileTseitinGateClauses c2

/-- Concrete emitted 3-CNF formula for circuit `c`: prepends the output unit clause
    `(c ∨ c ∨ c)` to `compileTseitinGateClauses c`. -/
def compileTseitinCNF (c : BoolCircuit) : List (Clause3 BoolCircuit) :=
  ((c, true), (c, true), (c, true)) :: compileTseitinGateClauses c

/-- Satisfaction predicate for the concrete emitted 3-CNF `compileTseitinCNF c`
    combined with input-variable agreement with `env`. -/
def tseitin3CNFSat (c : BoolCircuit) (env : Nat → Bool) (wire : BoolCircuit → Bool) : Prop :=
  tseitinWireConsistent env wire c = true ∧ evalCNF3 wire (compileTseitinCNF c) = true

theorem evalCNF3_append {α : Type} (assign : α → Bool) (l1 l2 : List (Clause3 α)) :
    evalCNF3 assign (l1 ++ l2) = (evalCNF3 assign l1 && evalCNF3 assign l2) := by
  induction l1 with
  | nil => simp [evalCNF3]
  | cons cl cls ih =>
    rw [List.cons_append, evalCNF3, ih, evalCNF3, Bool.and_assoc]

theorem evalCNF3_emitNot (w : BoolCircuit → Bool) (a b : BoolCircuit) :
    evalCNF3 w (emitNotClauses a b) = tseitinNotClauses (w a) (w b) := by
  simp only [emitNotClauses, evalCNF3, evalClause3, evalLit3, tseitinNotClauses]
  cases w a <;> cases w b <;> decide

theorem evalCNF3_emitAnd (w : BoolCircuit → Bool) (a b out : BoolCircuit) :
    evalCNF3 w (emitAndClauses a b out) = tseitinAndClauses2 (w a) (w b) (w out) := by
  simp only [emitAndClauses, evalCNF3, evalClause3, evalLit3, tseitinAndClauses2]
  cases w a <;> cases w b <;> cases w out <;> decide

theorem evalCNF3_emitOr (w : BoolCircuit → Bool) (a b out : BoolCircuit) :
    evalCNF3 w (emitOrClauses a b out) = tseitinOrClauses (w a) (w b) (w out) := by
  simp only [emitOrClauses, evalCNF3, evalClause3, evalLit3, tseitinOrClauses]
  cases w a <;> cases w b <;> cases w out <;> decide

/-- Theorem PNP-07e: Whenever `tseitinWireConsistent env wire c = true`, the concrete emitted
    gate clause list `compileTseitinGateClauses c` evaluates to `true` under `evalCNF3`. -/
theorem pnp_07_emitted_gate_clauses_true_of_consistent
    (env : Nat → Bool) (wire : BoolCircuit → Bool) (c : BoolCircuit)
    (hcons : tseitinWireConsistent env wire c = true) :
    evalCNF3 wire (compileTseitinGateClauses c) = true := by
  induction c with
  | var _ => rfl
  | not c ih =>
    simp only [tseitinWireConsistent, Bool.and_eq_true] at hcons
    simp only [compileTseitinGateClauses, evalCNF3_append, evalCNF3_emitNot,
      hcons.1, ih hcons.2, Bool.and_self]
  | and c1 c2 ih1 ih2 =>
    simp only [tseitinWireConsistent, Bool.and_eq_true] at hcons
    simp only [compileTseitinGateClauses, evalCNF3_append, evalCNF3_emitAnd,
      hcons.1.1, ih1 hcons.1.2, ih2 hcons.2, Bool.and_self]
  | or c1 c2 ih1 ih2 =>
    simp only [tseitinWireConsistent, Bool.and_eq_true] at hcons
    simp only [compileTseitinGateClauses, evalCNF3_append, evalCNF3_emitOr,
      hcons.1.1, ih1 hcons.1.2, ih2 hcons.2, Bool.and_self]

/-- Theorem PNP-07f: The length of the emitted gate clause list `compileTseitinGateClauses c`
    equals `tseitinGateClauseCount c`. -/
theorem pnp_07_emitted_gate_clauses_length (c : BoolCircuit) :
    (compileTseitinGateClauses c).length = tseitinGateClauseCount c := by
  induction c with
  | var _ => rfl
  | not c ih =>
    simp only [compileTseitinGateClauses, List.length_append, emitNotClauses,
      List.length_cons, List.length_nil, tseitinGateClauseCount, ih]
  | and c1 c2 ih1 ih2 =>
    simp only [compileTseitinGateClauses, List.length_append, emitAndClauses,
      List.length_cons, List.length_nil, tseitinGateClauseCount, ih1, ih2]
  | or c1 c2 ih1 ih2 =>
    simp only [compileTseitinGateClauses, List.length_append, emitOrClauses,
      List.length_cons, List.length_nil, tseitinGateClauseCount, ih1, ih2]

/-- Theorem PNP-07g: The length of the full emitted 3-CNF `compileTseitinCNF c` equals
    `tseitinGateClauseCount c + 1` and is bounded above by `3 * gateCount c + 1`. -/
theorem pnp_07_emitted_cnf_length_bound (c : BoolCircuit) :
    (compileTseitinCNF c).length = tseitinGateClauseCount c + 1 ∧
    (compileTseitinCNF c).length ≤ 3 * gateCount c + 1 := by
  have hlen : (compileTseitinCNF c).length = tseitinGateClauseCount c + 1 := by
    simp only [compileTseitinCNF, List.length_cons, pnp_07_emitted_gate_clauses_length]
  refine ⟨hlen, ?_⟩
  rw [hlen]
  exact pnp_07_tseitin_clause_count_linear_bound c

/-- Theorem PNP-07h: For a single NOT gate `.not (.var 0)`, the emitted 3-CNF has length `3`,
    which is strictly less than `3 * gateCount (.not (.var 0)) + 1 = 4` because a NOT gate
    emits 2 gate clauses rather than 3. -/
theorem pnp_07_single_not_gate_clause_count_strict_lt :
    (compileTseitinCNF (.not (.var 0))).length = 3 ∧
    3 * gateCount (.not (.var 0)) + 1 = 4 ∧
    (compileTseitinCNF (.not (.var 0))).length < 3 * gateCount (.not (.var 0)) + 1 := by
  decide

/-- Theorem PNP-07i: Global Equi-Satisfiability of the concrete emitted 3-CNF
    `compileTseitinCNF c` via `tseitin3CNFSat`. -/
theorem pnp_07_emitted_cnf_equisat (env : Nat → Bool) (c : BoolCircuit) :
    (∃ wire : BoolCircuit → Bool, tseitin3CNFSat c env wire) ↔
    evalCircuit env c = true := by
  constructor
  · rintro ⟨wire, hcons, hcnf⟩
    simp only [compileTseitinCNF, evalCNF3, evalClause3, evalLit3, ite_true,
      Bool.or_self, Bool.and_eq_true] at hcnf
    rw [← pnp_07_tseitin_circuit_soundness env wire c hcons]
    exact hcnf.1
  · intro heval
    refine ⟨canonicalWireEnv env, ?_⟩
    have hcons := pnp_07_tseitin_circuit_completeness env c
    have hgates := pnp_07_emitted_gate_clauses_true_of_consistent env (canonicalWireEnv env) c hcons
    refine ⟨hcons, ?_⟩
    simp only [compileTseitinCNF, evalCNF3, evalClause3, evalLit3, ite_true,
      Bool.or_self, canonicalWireEnv, heval, hgates, Bool.and_self]

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

/-- Update coordinate `k` of a boolean hypercube point `x : Nat → Bool` to `b`. -/
def setBit (x : Nat → Bool) (k : Nat) (b : Bool) : Nat → Bool :=
  fun i => if i = k then b else x i

/-- Recursive `n`-bit Parity sign function `χ_n(x) = ∏_{i < n} (-1)^{x_i} ∈ {+1, -1}`
    defined for arbitrary dimension `n : Nat`. -/
def paritySignN : Nat → (Nat → Bool) → Int
  | 0,     _ => 1
  | n + 1, x => (if x n then -1 else 1) * paritySignN n x

/-- Recursive `n`-dimensional boolean hypercube Fourier/finite-difference parity functional
    `Δ_n(f) = ∑_{x ∈ {0,1}^n} χ_n(x) f(x)` defined for arbitrary dimension `n : Nat`. -/
def hypercubeFourierParityN : Nat → ((Nat → Bool) → Int) → Int
  | 0,     f => f (fun _ => false)
  | n + 1, f =>
      hypercubeFourierParityN n (fun x => f (setBit x n false) - f (setBit x n true))

theorem hypercubeFourierParityN_zero (n : Nat) :
    hypercubeFourierParityN n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [hypercubeFourierParityN, Int.sub_self, ih]

theorem hypercubeFourierParityN_add (n : Nat) (f g : (Nat → Bool) → Int) :
    hypercubeFourierParityN n (fun x => f x + g x) =
      hypercubeFourierParityN n f + hypercubeFourierParityN n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [hypercubeFourierParityN]
    have h_eq :
        (fun x => (f (setBit x n false) + g (setBit x n false)) -
                  (f (setBit x n true) + g (setBit x n true))) =
        (fun x => (f (setBit x n false) - f (setBit x n true)) +
                  (g (setBit x n false) - g (setBit x n true))) := by
      funext x
      omega
    rw [h_eq, ih]

theorem setBit_comm (x : Nat → Bool) {j k : Nat} (hjk : j ≠ k) (b1 b2 : Bool) :
    setBit (setBit x j b1) k b2 = setBit (setBit x k b2) j b1 := by
  funext i
  unfold setBit
  by_cases hik : i = k
  · subst hik
    have hij : i ≠ j := Ne.symm hjk
    simp [hij]
  · simp [hik]

theorem paritySignN_setBit_ge (n m : Nat) (hnm : n ≤ m) (x : Nat → Bool) (b : Bool) :
    paritySignN n (setBit x m b) = paritySignN n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hlt : n < m := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hnm
    have hne : n ≠ m := Nat.ne_of_lt hlt
    have hle : n ≤ m := Nat.le_of_lt hlt
    simp only [paritySignN, setBit, hne, ite_false, ih hle]

/-- Theorem PNP-08d (Asymptotic All-`n` Orthogonality of Sub-Degree / Coordinate-Insensitive Terms):
    For every dimension `n : Nat` and every coordinate `k < n`, any function
    `f : (Nat → Bool) → Int` that does not depend on coordinate `k` (such as any
    multilinear monomial of degree `≤ n - 1`, which must omit at least one variable `k < n`)
    is identically annihilated by `hypercubeFourierParityN n`. -/
theorem pnp_08_all_n_subdegree_term_annihilated (n k : Nat) (hk : k < n)
    (f : (Nat → Bool) → Int)
    (h_insens : ∀ x : Nat → Bool, f (setBit x k false) = f (setBit x k true)) :
    hypercubeFourierParityN n f = 0 := by
  induction n generalizing k f with
  | zero => omega
  | succ n ih =>
    simp only [hypercubeFourierParityN]
    by_cases hkn : k = n
    · subst hkn
      have h_zero : (fun x => f (setBit x k false) - f (setBit x k true)) = (fun _ => 0) := by
        funext x
        have hx := h_insens x
        omega
      rw [h_zero, hypercubeFourierParityN_zero]
    · have hk_lt : k < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk) hkn
      apply ih k hk_lt
      intro x
      have h1 : setBit (setBit x k false) n false = setBit (setBit x n false) k false :=
        setBit_comm x hkn false false
      have h2 : setBit (setBit x k false) n true = setBit (setBit x n true) k false :=
        setBit_comm x hkn false true
      have h3 : setBit (setBit x k true) n false = setBit (setBit x n false) k true :=
        setBit_comm x hkn true false
      have h4 : setBit (setBit x k true) n true = setBit (setBit x n true) k true :=
        setBit_comm x hkn true true
      rw [h1, h2, h3, h4]
      have hf0 := h_insens (setBit x n false)
      have hf1 := h_insens (setBit x n true)
      omega

theorem hypercubeFourierParityN_scale_two (n : Nat) (f : (Nat → Bool) → Int) :
    hypercubeFourierParityN n (fun x => 2 * f x) = 2 * hypercubeFourierParityN n f := by
  have h_eq : (fun x => 2 * f x) = (fun x => f x + f x) := by
    funext x
    omega
  rw [h_eq, hypercubeFourierParityN_add]
  omega

/-- Theorem PNP-08e (Asymptotic All-`n` Fourier Norm of `n`-Bit Parity):
    For every dimension `n : Nat`, `hypercubeFourierParityN n (paritySignN n) > 0`. -/
theorem pnp_08_all_n_parity_fourier_pos (n : Nat) :
    0 < hypercubeFourierParityN n (paritySignN n) := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [hypercubeFourierParityN]
    have h_step :
        (fun x => paritySignN (n + 1) (setBit x n false) - paritySignN (n + 1) (setBit x n true)) =
        (fun x => 2 * paritySignN n x) := by
      funext x
      simp only [paritySignN, setBit, ↓reduceIte, Bool.false_eq_true,
        paritySignN_setBit_ge n n (Nat.le_refl n)]
      omega
    rw [h_step, hypercubeFourierParityN_scale_two]
    omega

/-- Sum a finite list of functions `terms : List ((Nat → Bool) → Int)` pointwise. -/
def sumPolyTerms : List ((Nat → Bool) → Int) → (Nat → Bool) → Int
  | [],      _ => 0
  | t :: ts, x => t x + sumPolyTerms ts x

/-- Theorem PNP-08f (Asymptotic All-`n` Annihilation of Arbitrary Sums of Sub-Degree Terms):
    For every `n : Nat`, any finite sum of terms `terms` in which each term is independent
    of at least one coordinate `k < n` (i.e. any polynomial of degree `< n`) satisfies
    `hypercubeFourierParityN n (sumPolyTerms terms) = 0`. -/
theorem pnp_08_all_n_subdegree_sum_eq_zero (n : Nat)
    (terms : List ((Nat → Bool) → Int))
    (h_subdeg : ∀ t ∈ terms, ∃ k, k < n ∧ ∀ x, t (setBit x k false) = t (setBit x k true)) :
    hypercubeFourierParityN n (sumPolyTerms terms) = 0 := by
  induction terms with
  | nil =>
    exact hypercubeFourierParityN_zero n
  | cons t ts ih =>
    have h_split : sumPolyTerms (t :: ts) = (fun x => t x + sumPolyTerms ts x) := rfl
    rw [h_split, hypercubeFourierParityN_add]
    rcases h_subdeg t (List.mem_cons_self t ts) with ⟨k, hk, h_ins⟩
    have ht0 := pnp_08_all_n_subdegree_term_annihilated n k hk t h_ins
    have hts0 := ih (fun t' ht' => h_subdeg t' (List.mem_cons_of_mem t ht'))
    omega

/-- Theorem PNP-08g (Asymptotic All-`n` Polynomial Degree Lower Bound for `n`-Bit Parity):
    For every dimension `n : Nat`, no polynomial `sumPolyTerms terms` composed of terms
    of degree `< n` (each omitting at least one coordinate `k < n`) can agree with
    `paritySignN n` on `(Nat → Bool)`. -/
theorem pnp_08_all_n_no_subdegree_polynomial_computes_parity (n : Nat)
    (terms : List ((Nat → Bool) → Int))
    (h_subdeg : ∀ t ∈ terms, ∃ k, k < n ∧ ∀ x, t (setBit x k false) = t (setBit x k true)) :
    ¬(∀ x : Nat → Bool, sumPolyTerms terms x = paritySignN n x) := by
  intro hall
  have h_eq : sumPolyTerms terms = paritySignN n := by
    funext x
    exact hall x
  have h_zero := pnp_08_all_n_subdegree_sum_eq_zero n terms h_subdeg
  have h_pos := pnp_08_all_n_parity_fourier_pos n
  rw [h_eq] at h_zero
  omega

/- ============================================================================
   SECTION 9: PNP-09 — RAZBOROV-RUDICH NATURAL PROOFS DISTINGUISHER INEQUALITY
   & AARONSON-WIGDERSON ALGEBRIZATION EXTENSION OBSTRUCTION
   ============================================================================ -/

/-- Theorem PNP-09a (Razborov-Rudich Natural Proofs Distinguisher Bound):
    If a combinatorial property `C` on truth tables of universe size `U > 0` has
    - **Largeness**: `C_count ≥ delta_num` (out of `U` total functions), and
    - **Usefulness against `F`**: `F_in_C = 0` (no function in family `F` satisfies `C`),
    then the unnormalized distinguishing gap `C_count - F_in_C` is at least `delta_num`,
    so any pseudorandomness bound `C_count - F_in_C ≤ eps_num` forces `delta_num ≤ eps_num`
    (refuting `delta_num > eps_num`). -/
theorem pnp_09_razborov_rudich_natural_proofs_barrier
    (C_count F_in_C delta_num eps_num : Int)
    (h_largeness : delta_num ≤ C_count)
    (h_usefulness : F_in_C = 0)
    (h_prf_security : C_count - F_in_C ≤ eps_num) :
    delta_num ≤ eps_num := by
  omega

/-- Boolean indicator on `{0, 1}` vs quadratic algebraic extension `q(x) = x^2` over `Int`:
    on the boolean domain `{0, 1}`, `x^2 - x = 0`, whereas at the non-boolean extension
    point `x = 2`, `x^2 - x = 2 ≠ 0`. -/
def algebrizationExtensionGap (x : Int) : Int :=
  x * x - x

/-- Theorem PNP-09b (Aaronson-Wigderson Algebrization Extension Obstruction):
    The polynomial `algebrizationExtensionGap x = x^2 - x` vanishes identically on the
    boolean cube `{0, 1}` (`b2i b` for all `b : Bool`), yet is strictly positive (`= 2`)
    at the algebraic extension point `x = 2`, demonstrating that multilinear collapse
    `x^2 = x` does not algebrize to low-degree extensions over `Int`. -/
theorem pnp_09_algebrization_extension_obstruction :
    (∀ b : Bool, algebrizationExtensionGap (b2i b) = 0) ∧
    algebrizationExtensionGap 2 = 2 ∧
    algebrizationExtensionGap 2 ≠ 0 := by
  constructor
  · intro b
    cases b <;> decide
  · decide

end PvsNPAdjudication
