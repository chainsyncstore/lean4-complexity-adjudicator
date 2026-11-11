import ComplexitySAT.Classes

/-! Execution and output-length bounds for finite multi-stack machines. -/

set_option autoImplicit false

namespace ComplexitySAT

open Turing Computability Polynomial Turing.TM2.Stmt

theorem polyEvalMono (p : Polynomial ℕ) : ∀ n m : ℕ, n ≤ m → p.eval n ≤ p.eval m := by
  intro n m h
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    simp only [Polynomial.eval_add]
    exact Nat.add_le_add hp hq
  · intro k a
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left a (Nat.pow_le_pow_left h k)

def stmtMaxPush {K : Type*} {Γ : K → Type*} {Λ σ : Type*} :
    Turing.TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => 1 + stmtMaxPush q
  | .peek _ _ q => stmtMaxPush q
  | .pop _ _ q => stmtMaxPush q
  | .load _ q => stmtMaxPush q
  | .branch _ q₁ q₂ => max (stmtMaxPush q₁) (stmtMaxPush q₂)
  | .goto _ => 0
  | .halt => 0

noncomputable def tmMaxPush (tm : FinTM2) : ℕ := by
  letI : Fintype tm.Λ := tm.ΛFin
  exact Finset.univ.sup (fun l => stmtMaxPush (tm.m l))

theorem update_cons_length_le {K : Type*} [DecidableEq K] {Γ : K → Type*}
    (S : ∀ k, List (Γ k)) (k' k : K) (a : Γ k') :
    ((Function.update S k' (a :: S k')) k).length ≤ (S k).length + 1 := by
  by_cases h : k = k'
  · subst h; simp [Function.update_self]
  · simp [Function.update_of_ne h]

theorem update_tail_length_le {K : Type*} [DecidableEq K] {Γ : K → Type*}
    (S : ∀ k, List (Γ k)) (k' k : K) :
    ((Function.update S k' (S k').tail) k).length ≤ (S k).length := by
  by_cases h : k = k'
  · subst h; simp [Function.update_self, List.length_tail]
  · simp [Function.update_of_ne h]

theorem stepAux_stk_length_le {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}
    (q : Turing.TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((Turing.TM2.stepAux q v S).stk k).length ≤ (S k).length + stmtMaxPush q := by
  induction q generalizing v S with
  | push k' f q ih =>
    dsimp [Turing.TM2.stepAux, stmtMaxPush]
    have h1 := ih v (Function.update S k' (f v :: S k'))
    have h2 := update_cons_length_le S k' k (f v)
    omega
  | peek k' f q ih =>
    dsimp [Turing.TM2.stepAux, stmtMaxPush]
    exact ih (f v (S k').head?) S
  | pop k' f q ih =>
    dsimp [Turing.TM2.stepAux, stmtMaxPush]
    have h1 := ih (f v (S k').head?) (Function.update S k' (S k').tail)
    have h2 := update_tail_length_le S k' k
    omega
  | load s q ih =>
    dsimp [Turing.TM2.stepAux, stmtMaxPush]
    exact ih (s v) S
  | branch f q₁ q₂ ih₁ ih₂ =>
    dsimp [Turing.TM2.stepAux, stmtMaxPush]
    cases f v <;> dsimp [cond]
    · exact le_trans (ih₂ v S) (Nat.add_le_add_left (Nat.le_max_right _ _) _)
    · exact le_trans (ih₁ v S) (Nat.add_le_add_left (Nat.le_max_left _ _) _)
  | goto l =>
    simp [Turing.TM2.stepAux, stmtMaxPush]
  | halt =>
    simp [Turing.TM2.stepAux, stmtMaxPush]

theorem stmtMaxPush_le_tmMaxPush (tm : FinTM2) (l : tm.Λ) :
    stmtMaxPush (tm.m l) ≤ tmMaxPush tm := by
  letI : Fintype tm.Λ := tm.ΛFin
  exact Finset.le_sup (f := fun l => stmtMaxPush (tm.m l)) (Finset.mem_univ l)

theorem step_stk_length_le (tm : FinTM2) (c c' : tm.Cfg) (k : tm.K)
    (h : tm.step c = some c') :
    (c'.stk k).length ≤ (c.stk k).length + tmMaxPush tm := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none =>
    simp [FinTM2.step, Turing.TM2.step] at h
  | some l =>
    simp only [FinTM2.step, Turing.TM2.step, Option.some.injEq] at h
    subst h
    exact le_trans (stepAux_stk_length_le (tm.m l) v S k) (Nat.add_le_add_left (stmtMaxPush_le_tmMaxPush tm l) _)

theorem iterate_step_none (tm : FinTM2) (t : ℕ) :
    (flip bind tm.step)^[t] none = none := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply]
    exact ih

theorem iterate_step_stk_length_le (tm : FinTM2) (t : ℕ) (c c' : tm.Cfg) (k : tm.K)
    (h : (flip bind tm.step)^[t] (some c) = some c') :
    (c'.stk k).length ≤ (c.stk k).length + t * tmMaxPush tm := by
  induction t generalizing c with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Option.some.injEq] at h
    subst h
    simp
  | succ t ih =>
    rw [Function.iterate_succ_apply] at h
    change (flip bind tm.step)^[t] (tm.step c) = some c' at h
    cases hs : tm.step c with
    | none =>
      rw [hs, iterate_step_none] at h
      cases h
    | some c1 =>
      rw [hs] at h
      have h1 := step_stk_length_le tm c c1 k hs
      have h2 := ih c1 h
      have hmul : (t + 1) * tmMaxPush tm = tmMaxPush tm + t * tmMaxPush tm := by
        rw [Nat.add_one_mul, Nat.add_comm]
      omega

theorem initList_stk_length_le (tm : FinTM2) (s : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((Turing.initList tm s).stk k).length ≤ s.length := by
  dsimp [Turing.initList]
  split_ifs with h
  · subst h; exact le_rfl
  · simp

theorem haltList_stk_k₁ (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    (Turing.haltList tm s).stk tm.k₁ = s := by
  simp [Turing.haltList]

theorem tm2_output_length_poly :
    ∀ (f : ComplexitySAT.BitString → ComplexitySAT.BitString),
      Nonempty (Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f) →
      ∃ p : Polynomial ℕ, ∀ x : ComplexitySAT.BitString, (f x).length ≤ p.eval x.length := by
  rintro f ⟨hf⟩
  refine ⟨Polynomial.X + hf.time * Polynomial.C (tmMaxPush hf.tm), fun x => ?_⟩
  have hout := hf.outputsFun x
  have hiter := iterate_step_stk_length_le hf.tm hout.steps _ _ hf.tm.k₁ hout.evals_in_steps
  dsimp [ComplexitySAT.finEncodingBitString] at hiter
  rw [haltList_stk_k₁, List.length_map] at hiter
  have hinit := initList_stk_length_le hf.tm (List.map (⇑hf.inputAlphabet.symm) x) hf.tm.k₁
  rw [List.length_map] at hinit
  have hsteps : hout.steps ≤ hf.time.eval x.length := by
    simpa [ComplexitySAT.finEncodingBitString] using hout.steps_le_m
  have hmul : hout.steps * tmMaxPush hf.tm ≤ (hf.time.eval x.length) * tmMaxPush hf.tm :=
    Nat.mul_le_mul_right _ hsteps
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
  omega

def evalsRefl {tm : FinTM2} (c : tm.Cfg) : Turing.EvalsToInTime tm.step c (some c) 0 :=
  Turing.EvalsToInTime.refl tm.step c

def evalsInOne {tm : FinTM2} {c c' : tm.Cfg} (h : tm.step c = some c') :
    Turing.EvalsToInTime tm.step c (some c') 1 :=
  ⟨⟨1, h⟩, le_rfl⟩

def evalsTrans {tm : FinTM2} {c₁ c₂ c₃ : tm.Cfg} {m₁ m₂ : ℕ}
    (h₁ : Turing.EvalsToInTime tm.step c₁ (some c₂) m₁)
    (h₂ : Turing.EvalsToInTime tm.step c₂ (some c₃) m₂) :
    Turing.EvalsToInTime tm.step c₁ (some c₃) (m₂ + m₁) :=
  Turing.EvalsToInTime.trans tm.step m₁ m₂ c₁ c₂ (some c₃) h₁ h₂

def evalsMono {tm : FinTM2} {a : tm.Cfg} {b : Option tm.Cfg} {m m' : ℕ}
    (h : Turing.EvalsToInTime tm.step a b m) (hle : m ≤ m') :
    Turing.EvalsToInTime tm.step a b m' :=
  ⟨h.toEvalsTo, le_trans h.steps_le_m hle⟩

end ComplexitySAT
