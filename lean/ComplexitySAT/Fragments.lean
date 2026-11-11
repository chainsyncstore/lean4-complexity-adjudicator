import ComplexitySAT.CNF

/-! Syntactic 2-CNF and Horn predicates, and an explicit counterexample to diagonal selector stability. -/

set_option autoImplicit false

namespace ComplexitySAT

/-- Clause of length `n` that negates the first `n` bits of assignment `w`:
    `negateAssignmentClause n w` is satisfied by `v` iff `v` disagrees with `w`
    on at least one variable index `i < n`. -/
def negateAssignmentClause : Nat → BitString → Clause
  | 0, _ => []
  | n + 1, w => (n, !(w.getD n false)) :: negateAssignmentClause n w

/-- Diagonal CNF formula against a finite list of candidate witnesses `W` at prefix length `n`. -/
def diagonalCNF (n : Nat) (W : List BitString) : CNF :=
  W.map (negateAssignmentClause n)

/-- Diagonal self-consistency condition for an input-adaptive witness selector
    `selector : BitString → List BitString` at prefix parameter `n` and input `x`:
    evaluating `selector` on the diagonalized formula `cnfCode (diagonalCNF n (selector x))`
    yields a witness list covered by `selector x`. Without such a fixed-point or stability
    condition, `diagonalCNF n (selector x)` changes the input presented to `selector`. -/
def DiagonalSelectorStableAt (n : Nat) (selector : BitString → List BitString) (x : BitString) : Prop :=
  ∀ w ∈ selector (cnfCode (diagonalCNF n (selector x))), w ∈ selector x

/-- Tractable control predicate: a clause has at most 2 literals (2-SAT). -/
def Is2SATClause (c : Clause) : Prop :=
  c.length ≤ 2

/-- Tractable control predicate: every clause in `f : CNF` has at most 2 literals (2-SAT). -/
def Is2SATCNF (f : CNF) : Prop :=
  ∀ c ∈ f, Is2SATClause c

/-- Tractable control predicate: a clause has at most 1 positive literal (Horn-SAT). -/
def IsHornClause (c : Clause) : Prop :=
  (c.filter (fun l => l.2 = true)).length ≤ 1

/-- Tractable control predicate: every clause in `f : CNF` is a Horn clause (Horn-SAT). -/
def IsHornCNF (f : CNF) : Prop :=
  ∀ c ∈ f, IsHornClause c

def positiveUnitCode : ComplexitySAT.BitString :=
  ComplexitySAT.cnfCode (ComplexitySAT.diagonalCNF 1 [[false]])

def negativeUnitCode : ComplexitySAT.BitString :=
  ComplexitySAT.cnfCode (ComplexitySAT.diagonalCNF 1 [[true]])

def responsiveUnitGenerator (x : ComplexitySAT.BitString) : ComplexitySAT.BitString :=
  if x = positiveUnitCode then [true] else [false]

theorem singleton_diagonal_fragments (w : BitString) :
    Is2SATCNF (diagonalCNF 1 [w]) ∧ IsHornCNF (diagonalCNF 1 [w]) := by
  refine ⟨?_, ?_⟩
  · simp [ComplexitySAT.Is2SATCNF, ComplexitySAT.Is2SATClause,
      ComplexitySAT.diagonalCNF, ComplexitySAT.negateAssignmentClause]
  · intro c hc
    have heq : c = ComplexitySAT.negateAssignmentClause 1 w := by
      simpa [ComplexitySAT.diagonalCNF] using hc
    rw [heq]
    unfold ComplexitySAT.IsHornClause
    exact Nat.le_trans (List.length_filter_le ..)
      (by simp [ComplexitySAT.negateAssignmentClause])

theorem responsiveUnitGenerator_not_stable (x : BitString) :
    ¬ DiagonalSelectorStableAt 1 (fun y => [responsiveUnitGenerator y]) x := by
  intro h
  unfold ComplexitySAT.DiagonalSelectorStableAt at h
  have hdiff : ComplexitySAT.negativeUnitCode ≠ ComplexitySAT.positiveUnitCode := by
    decide
  have heq := h
    (ComplexitySAT.responsiveUnitGenerator
      (ComplexitySAT.cnfCode
        (ComplexitySAT.diagonalCNF 1
          [ComplexitySAT.responsiveUnitGenerator x])))
    (by simp)
  simp only [List.mem_singleton] at heq
  by_cases hx : x = ComplexitySAT.positiveUnitCode
  · subst hx
    have hg : ComplexitySAT.responsiveUnitGenerator
        ComplexitySAT.positiveUnitCode = [true] := by
      simp [ComplexitySAT.responsiveUnitGenerator]
    rw [hg] at heq
    change ComplexitySAT.responsiveUnitGenerator
        ComplexitySAT.negativeUnitCode = [true] at heq
    simp [ComplexitySAT.responsiveUnitGenerator, hdiff] at heq
  · have hg : ComplexitySAT.responsiveUnitGenerator x = [false] := by
      simp [ComplexitySAT.responsiveUnitGenerator, hx]
    rw [hg] at heq
    change ComplexitySAT.responsiveUnitGenerator
        ComplexitySAT.positiveUnitCode = [false] at heq
    simp [ComplexitySAT.responsiveUnitGenerator] at heq

end ComplexitySAT
