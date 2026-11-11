import ComplexitySAT.MachineBounds

/-! Polynomial-time composition through the binary encoding. The composite simulates the first machine, transfers its output, then simulates the second. -/

set_option autoImplicit false

namespace ComplexitySAT

open Turing Computability Polynomial Turing.TM2.Stmt

instance instFintypeTMΛ (tm : FinTM2) : Fintype tm.Λ := tm.ΛFin
instance instFintypeTMK (tm : FinTM2) : Fintype tm.K := tm.kFin
instance instFintypeTMσ (tm : FinTM2) : Fintype tm.σ := tm.σFin
instance instFintypeTMΓk₀ (tm : FinTM2) : Fintype (tm.Γ tm.k₀) := tm.Γk₀Fin

abbrev CompK (K₁ K₂ : Type) := Option (K₁ ⊕ K₂)
abbrev CompΛ (Λ₁ Λ₂ : Type) := (Λ₁ ⊕ Λ₂) ⊕ Bool
abbrev Compσ (σ₁ σ₂ : Type) := Option Bool × σ₁ × σ₂

def CompΓ {K₁ K₂ : Type} (Γ₁ : K₁ → Type) (Γ₂ : K₂ → Type) : CompK K₁ K₂ → Type
  | none => Bool
  | some (Sum.inl k) => Γ₁ k
  | some (Sum.inr k) => Γ₂ k

def liftStmt₁ {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {Γ₂ : K₂ → Type} {Λ₁ Λ₂ σ₁ σ₂ : Type} :
    Turing.TM2.Stmt Γ₁ Λ₁ σ₁ →
    Turing.TM2.Stmt (CompΓ Γ₁ Γ₂) (CompΛ Λ₁ Λ₂) (Compσ σ₁ σ₂)
  | .push k qf q => .push (some (Sum.inl k)) (fun s => qf s.2.1) (liftStmt₁ q)
  | .peek k qf q => .peek (some (Sum.inl k)) (fun s x => (s.1, qf s.2.1 x, s.2.2)) (liftStmt₁ q)
  | .pop k qf q => .pop (some (Sum.inl k)) (fun s x => (s.1, qf s.2.1 x, s.2.2)) (liftStmt₁ q)
  | .load a q => .load (fun s => (s.1, a s.2.1, s.2.2)) (liftStmt₁ q)
  | .branch p q₁ q₂ => .branch (fun s => p s.2.1) (liftStmt₁ q₁) (liftStmt₁ q₂)
  | .goto l => .goto (fun s => Sum.inl (Sum.inl (l s.2.1)))
  | .halt => .goto (fun _ => Sum.inr false)

def liftStmt₂ {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {Γ₂ : K₂ → Type} {Λ₁ Λ₂ σ₁ σ₂ : Type} :
    Turing.TM2.Stmt Γ₂ Λ₂ σ₂ →
    Turing.TM2.Stmt (CompΓ Γ₁ Γ₂) (CompΛ Λ₁ Λ₂) (Compσ σ₁ σ₂)
  | .push k qf q => .push (some (Sum.inr k)) (fun s => qf s.2.2) (liftStmt₂ q)
  | .peek k qf q => .peek (some (Sum.inr k)) (fun s x => (s.1, s.2.1, qf s.2.2 x)) (liftStmt₂ q)
  | .pop k qf q => .pop (some (Sum.inr k)) (fun s x => (s.1, s.2.1, qf s.2.2 x)) (liftStmt₂ q)
  | .load a q => .load (fun s => (s.1, s.2.1, a s.2.2)) (liftStmt₂ q)
  | .branch p q₁ q₂ => .branch (fun s => p s.2.2) (liftStmt₂ q₁) (liftStmt₂ q₂)
  | .goto l => .goto (fun s => Sum.inl (Sum.inr (l s.2.2)))
  | .halt => .halt

def bridgeRevStmt {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {Γ₂ : K₂ → Type} {Λ₁ Λ₂ σ₁ σ₂ : Type}
    (k₁ : K₁) (toBool : Γ₁ k₁ → Bool) :
    Turing.TM2.Stmt (CompΓ Γ₁ Γ₂) (CompΛ Λ₁ Λ₂) (Compσ σ₁ σ₂) :=
  .pop (some (Sum.inl k₁)) (fun s top => (top.map toBool, s.2.1, s.2.2))
    (.branch (fun s => s.1.isSome)
      (.push none (fun s => s.1.getD false)
        (.load (fun s => (none, s.2.1, s.2.2))
          (.goto (fun _ => Sum.inr false))))
      (.load (fun s => (none, s.2.1, s.2.2))
        (.goto (fun _ => Sum.inr true))))

def bridgeCopyStmt {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {Γ₂ : K₂ → Type} {Λ₁ Λ₂ σ₁ σ₂ : Type}
    (k₀ : K₂) (fromBool : Bool → Γ₂ k₀) (main₂ : Λ₂) :
    Turing.TM2.Stmt (CompΓ Γ₁ Γ₂) (CompΛ Λ₁ Λ₂) (Compσ σ₁ σ₂) :=
  .pop none (fun s top => (top, s.2.1, s.2.2))
    (.branch (fun s => s.1.isSome)
      (.push (some (Sum.inr k₀)) (fun s => fromBool (s.1.getD false))
        (.load (fun s => (none, s.2.1, s.2.2))
          (.goto (fun _ => Sum.inr true))))
      (.load (fun s => (none, s.2.1, s.2.2))
        (.goto (fun _ => Sum.inl (Sum.inr main₂)))))

def compTM {β : Type} {eb : Computability.FinEncoding β}
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g) : FinTM2 where
  K := CompK hf.tm.K hg.tm.K
  k₀ := some (Sum.inl hf.tm.k₀)
  k₁ := some (Sum.inr hg.tm.k₁)
  Γ := CompΓ hf.tm.Γ hg.tm.Γ
  Λ := CompΛ hf.tm.Λ hg.tm.Λ
  main := Sum.inl (Sum.inl hf.tm.main)
  σ := Compσ hf.tm.σ hg.tm.σ
  initialState := (none, hf.tm.initialState, hg.tm.initialState)
  Γk₀Fin := hf.tm.Γk₀Fin
  m l := match l with
    | Sum.inl (Sum.inl l₁) => liftStmt₁ (hf.tm.m l₁)
    | Sum.inl (Sum.inr l₂) => liftStmt₂ (hg.tm.m l₂)
    | Sum.inr false => bridgeRevStmt hf.tm.k₁ hf.outputAlphabet.toFun
    | Sum.inr true => bridgeCopyStmt hg.tm.k₀ hg.inputAlphabet.invFun hg.tm.main

def embedOptΛ₁ {Λ₁ Λ₂ : Type} : Option Λ₁ → Option (CompΛ Λ₁ Λ₂)
  | some l => some (Sum.inl (Sum.inl l))
  | none => some (Sum.inr false)

def embedStk₁ {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {Γ₂ : K₂ → Type}
    (S : ∀ k, List (Γ₁ k)) : ∀ k : CompK K₁ K₂, List (CompΓ Γ₁ Γ₂ k)
  | none => []
  | some (Sum.inl k) => S k
  | some (Sum.inr _) => []

def embedCfg₁ {β : Type} {eb : Computability.FinEncoding β}
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g)
    (c : hf.tm.Cfg) : (compTM hf hg).Cfg :=
  ⟨embedOptΛ₁ c.l, (none, c.var, hg.tm.initialState), embedStk₁ c.stk⟩

theorem embedStk₁_update {K₁ K₂ : Type} [DecidableEq K₁] [DecidableEq K₂]
    {Γ₁ : K₁ → Type} {Γ₂ : K₂ → Type}
    (S : ∀ k, List (Γ₁ k)) (k : K₁) (val : List (Γ₁ k)) :
    Function.update (embedStk₁ (K₂ := K₂) (Γ₂ := Γ₂) S) (some (Sum.inl k)) val =
      embedStk₁ (Function.update S k val) := by
  funext idx
  rcases idx with _ | ⟨k' | k'⟩
  · simp [embedStk₁]
  · by_cases h : k' = k
    · subst h; simp [embedStk₁]
    · have hne : (some (Sum.inl k') : CompK K₁ K₂) ≠ some (Sum.inl k) := by simp [h]
      rw [Function.update_of_ne hne]
      dsimp [embedStk₁]
      rw [Function.update_of_ne h]
  · simp [embedStk₁]

theorem stepAux_liftStmt₁ {β : Type} {eb : Computability.FinEncoding β}
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g)
    (q : hf.tm.Stmt) (v : hf.tm.σ) (S : ∀ k, List (hf.tm.Γ k)) :
    Turing.TM2.stepAux (liftStmt₁ q) (none, v, hg.tm.initialState) (embedStk₁ S) =
      embedCfg₁ hf hg (Turing.TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k qf q ih =>
    dsimp [liftStmt₁, Turing.TM2.stepAux]
    rw [embedStk₁_update]
    exact ih v (Function.update S k (qf v :: S k))
  | peek k qf q ih =>
    dsimp [liftStmt₁, Turing.TM2.stepAux, embedStk₁]
    exact ih (qf v (S k).head?) S
  | pop k qf q ih =>
    dsimp [liftStmt₁, Turing.TM2.stepAux, embedStk₁]
    rw [embedStk₁_update]
    exact ih (qf v (S k).head?) (Function.update S k (S k).tail)
  | load a q ih =>
    dsimp [liftStmt₁, Turing.TM2.stepAux]
    exact ih (a v) S
  | branch p q₁ q₂ ih₁ ih₂ =>
    dsimp [liftStmt₁, Turing.TM2.stepAux]
    cases p v <;> dsimp [cond]
    · exact ih₂ v S
    · exact ih₁ v S
  | goto l =>
    rfl
  | halt =>
    rfl

theorem compTM_step_embedCfg₁ {β : Type} {eb : Computability.FinEncoding β}
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g)
    (c c' : hf.tm.Cfg) (h : hf.tm.step c = some c') :
    (compTM hf hg).step (embedCfg₁ hf hg c) = some (embedCfg₁ hf hg c') := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none =>
    simp [FinTM2.step, Turing.TM2.step] at h
  | some l =>
    simp only [FinTM2.step, Turing.TM2.step, Option.some.injEq] at h
    subst h
    change some (Turing.TM2.stepAux (liftStmt₁ (hf.tm.m l)) (none, v, hg.tm.initialState) (embedStk₁ S)) = _
    rw [stepAux_liftStmt₁]

theorem compTM_iterate_embedCfg₁ {β : Type} {eb : Computability.FinEncoding β}
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g)
    (t : ℕ) (c c' : hf.tm.Cfg) (h : (flip bind hf.tm.step)^[t] (some c) = some c') :
    (flip bind (compTM hf hg).step)^[t] (some (embedCfg₁ hf hg c)) = some (embedCfg₁ hf hg c') := by
  induction t generalizing c with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Option.some.injEq] at h
    subst h
    rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    change (flip bind hf.tm.step)^[t] (hf.tm.step c) = some c' at h
    cases hs : hf.tm.step c with
    | none =>
      rw [hs, iterate_step_none] at h
      cases h
    | some c1 =>
      rw [hs] at h
      change (flip bind (compTM hf hg).step)^[t] ((compTM hf hg).step (embedCfg₁ hf hg c)) = _
      rw [compTM_step_embedCfg₁ hf hg c c1 hs]
      exact ih c1 h

def compTM_evals_phase1 {β : Type} {eb : Computability.FinEncoding β}
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g)
    {c c' : hf.tm.Cfg} {m : ℕ} (h : Turing.EvalsToInTime hf.tm.step c (some c') m) :
    Turing.EvalsToInTime (compTM hf hg).step (embedCfg₁ hf hg c) (some (embedCfg₁ hf hg c')) m :=
  ⟨⟨h.steps, compTM_iterate_embedCfg₁ hf hg h.steps c c' h.evals_in_steps⟩, h.steps_le_m⟩

def embedOptΛ₂ {Λ₁ Λ₂ : Type} : Option Λ₂ → Option (CompΛ Λ₁ Λ₂)
  | some l => some (Sum.inl (Sum.inr l))
  | none => none

def embedStk₂ {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {Γ₂ : K₂ → Type}
    (S : ∀ k, List (Γ₂ k)) : ∀ k : CompK K₁ K₂, List (CompΓ Γ₁ Γ₂ k)
  | none => []
  | some (Sum.inl _) => []
  | some (Sum.inr k) => S k

def embedCfg₂ {β : Type} {eb : Computability.FinEncoding β}
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g)
    (c : hg.tm.Cfg) : (compTM hf hg).Cfg :=
  ⟨embedOptΛ₂ c.l, (none, hf.tm.initialState, c.var), embedStk₂ c.stk⟩

theorem embedStk₂_update {K₁ K₂ : Type} [DecidableEq K₁] [DecidableEq K₂]
    {Γ₁ : K₁ → Type} {Γ₂ : K₂ → Type}
    (S : ∀ k, List (Γ₂ k)) (k : K₂) (val : List (Γ₂ k)) :
    Function.update (embedStk₂ (K₁ := K₁) (Γ₁ := Γ₁) S) (some (Sum.inr k)) val =
      embedStk₂ (Function.update S k val) := by
  funext idx
  rcases idx with _ | ⟨k' | k'⟩
  · simp [embedStk₂]
  · simp [embedStk₂]
  · by_cases h : k' = k
    · subst h; simp [embedStk₂]
    · have hne : (some (Sum.inr k') : CompK K₁ K₂) ≠ some (Sum.inr k) := by simp [h]
      rw [Function.update_of_ne hne]
      dsimp [embedStk₂]
      rw [Function.update_of_ne h]

theorem stepAux_liftStmt₂ {β : Type} {eb : Computability.FinEncoding β}
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g)
    (q : hg.tm.Stmt) (v : hg.tm.σ) (S : ∀ k, List (hg.tm.Γ k)) :
    Turing.TM2.stepAux (liftStmt₂ q) (none, hf.tm.initialState, v) (embedStk₂ S) =
      embedCfg₂ hf hg (Turing.TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k qf q ih =>
    dsimp [liftStmt₂, Turing.TM2.stepAux]
    rw [embedStk₂_update]
    exact ih v (Function.update S k (qf v :: S k))
  | peek k qf q ih =>
    dsimp [liftStmt₂, Turing.TM2.stepAux, embedStk₂]
    exact ih (qf v (S k).head?) S
  | pop k qf q ih =>
    dsimp [liftStmt₂, Turing.TM2.stepAux, embedStk₂]
    rw [embedStk₂_update]
    exact ih (qf v (S k).head?) (Function.update S k (S k).tail)
  | load a q ih =>
    dsimp [liftStmt₂, Turing.TM2.stepAux]
    exact ih (a v) S
  | branch p q₁ q₂ ih₁ ih₂ =>
    dsimp [liftStmt₂, Turing.TM2.stepAux]
    cases p v <;> dsimp [cond]
    · exact ih₂ v S
    · exact ih₁ v S
  | goto l =>
    rfl
  | halt =>
    rfl

theorem compTM_step_embedCfg₂ {β : Type} {eb : Computability.FinEncoding β}
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g)
    (c c' : hg.tm.Cfg) (h : hg.tm.step c = some c') :
    (compTM hf hg).step (embedCfg₂ hf hg c) = some (embedCfg₂ hf hg c') := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none =>
    simp [FinTM2.step, Turing.TM2.step] at h
  | some l =>
    simp only [FinTM2.step, Turing.TM2.step, Option.some.injEq] at h
    subst h
    change some (Turing.TM2.stepAux (liftStmt₂ (hg.tm.m l)) (none, hf.tm.initialState, v) (embedStk₂ S)) = _
    rw [stepAux_liftStmt₂]

theorem compTM_iterate_embedCfg₂ {β : Type} {eb : Computability.FinEncoding β}
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g)
    (t : ℕ) (c c' : hg.tm.Cfg) (h : (flip bind hg.tm.step)^[t] (some c) = some c') :
    (flip bind (compTM hf hg).step)^[t] (some (embedCfg₂ hf hg c)) = some (embedCfg₂ hf hg c') := by
  induction t generalizing c with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Option.some.injEq] at h
    subst h
    rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    change (flip bind hg.tm.step)^[t] (hg.tm.step c) = some c' at h
    cases hs : hg.tm.step c with
    | none =>
      rw [hs, iterate_step_none] at h
      cases h
    | some c1 =>
      rw [hs] at h
      change (flip bind (compTM hf hg).step)^[t] ((compTM hf hg).step (embedCfg₂ hf hg c)) = _
      rw [compTM_step_embedCfg₂ hf hg c c1 hs]
      exact ih c1 h

def compTM_evals_phase3 {β : Type} {eb : Computability.FinEncoding β}
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g)
    {c c' : hg.tm.Cfg} {m : ℕ} (h : Turing.EvalsToInTime hg.tm.step c (some c') m) :
    Turing.EvalsToInTime (compTM hf hg).step (embedCfg₂ hf hg c) (some (embedCfg₂ hf hg c')) m :=
  ⟨⟨h.steps, compTM_iterate_embedCfg₂ hf hg h.steps c c' h.evals_in_steps⟩, h.steps_le_m⟩

-- Phase 2: Bridge between hf.tm haltList and hg.tm initList

def bridgeStk {β : Type} {eb : Computability.FinEncoding β}
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g)
    (s1 : List (hf.tm.Γ hf.tm.k₁)) (smid : List Bool) (s2 : List (hg.tm.Γ hg.tm.k₀)) :
    ∀ k : CompK hf.tm.K hg.tm.K, List (CompΓ hf.tm.Γ hg.tm.Γ k)
  | none => smid
  | some (Sum.inl k) =>
    @dite (List (hf.tm.Γ k)) (k = hf.tm.k₁) (hf.tm.kDecidableEq k hf.tm.k₁)
      (fun h => by rw [h]; exact s1) (fun _ => [])
  | some (Sum.inr k) =>
    @dite (List (hg.tm.Γ k)) (k = hg.tm.k₀) (hg.tm.kDecidableEq k hg.tm.k₀)
      (fun h => by rw [h]; exact s2) (fun _ => [])

def bridgeCfg {β : Type} {eb : Computability.FinEncoding β}
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g)
    (l : Option (CompΛ hf.tm.Λ hg.tm.Λ))
    (s1 : List (hf.tm.Γ hf.tm.k₁)) (smid : List Bool) (s2 : List (hg.tm.Γ hg.tm.k₀)) :
    (compTM hf hg).Cfg :=
  ⟨l, (none, hf.tm.initialState, hg.tm.initialState), bridgeStk hf hg s1 smid s2⟩

theorem bridgeCfg_ext {β : Type} {eb : Computability.FinEncoding β}
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g)
    {l : Option (CompΛ hf.tm.Λ hg.tm.Λ)}
    {s1 : List (hf.tm.Γ hf.tm.k₁)} {smid : List Bool} {s2 : List (hg.tm.Γ hg.tm.k₀)}
    {stk : ∀ k : CompK hf.tm.K hg.tm.K, List (CompΓ hf.tm.Γ hg.tm.Γ k)}
    (h : ∀ k, stk k = bridgeStk hf hg s1 smid s2 k) :
    (⟨l, (none, hf.tm.initialState, hg.tm.initialState), stk⟩ : (compTM hf hg).Cfg) =
      bridgeCfg hf hg l s1 smid s2 := by
  unfold bridgeCfg
  congr 1
  funext k
  exact h k

theorem bridge_step_rev_nil {β : Type} {eb : Computability.FinEncoding β}
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g)
    (smid : List Bool) :
    (compTM hf hg).step (bridgeCfg hf hg (some (Sum.inr false)) [] smid []) =
      some (bridgeCfg hf hg (some (Sum.inr true)) [] smid []) := by
  dsimp [FinTM2.step, Turing.TM2.step, compTM, bridgeCfg, bridgeRevStmt, Turing.TM2.stepAux]
  have hhead : (bridgeStk hf hg [] smid [] (some (Sum.inl hf.tm.k₁))).head? = none := by
    simp [bridgeStk]
  rw [hhead]
  dsimp [Option.map, Option.isSome, cond]
  refine congrArg some (bridgeCfg_ext hf hg (fun idx => ?_))
  rcases idx with _ | ⟨k | k⟩
  · simp [bridgeStk]
  · by_cases hk : k = hf.tm.k₁
    · subst hk; simp [bridgeStk]
    · have hne : (some (Sum.inl k) : CompK hf.tm.K hg.tm.K) ≠ some (Sum.inl hf.tm.k₁) := by simp [hk]
      rw [Function.update_of_ne hne]
  · simp [bridgeStk]

theorem bridge_step_rev_cons {β : Type} {eb : Computability.FinEncoding β}
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g)
    (a : hf.tm.Γ hf.tm.k₁) (s1 : List (hf.tm.Γ hf.tm.k₁)) (smid : List Bool) :
    (compTM hf hg).step (bridgeCfg hf hg (some (Sum.inr false)) (a :: s1) smid []) =
      some (bridgeCfg hf hg (some (Sum.inr false)) s1 (hf.outputAlphabet.toFun a :: smid) []) := by
  dsimp [FinTM2.step, Turing.TM2.step, compTM, bridgeCfg, bridgeRevStmt, Turing.TM2.stepAux]
  have hhead : (bridgeStk hf hg (a :: s1) smid [] (some (Sum.inl hf.tm.k₁))).head? = some a := by
    simp [bridgeStk]
  rw [hhead]
  dsimp [Option.map, Option.isSome, Option.getD, cond]
  refine congrArg some (bridgeCfg_ext hf hg (fun idx => ?_))
  rcases idx with _ | ⟨k | k⟩
  · simp [bridgeStk]
  · by_cases hk : k = hf.tm.k₁
    · subst hk
      have hne_none : (some (Sum.inl hf.tm.k₁) : CompK hf.tm.K hg.tm.K) ≠ none := by simp
      rw [Function.update_of_ne hne_none, Function.update_self]
      simp [bridgeStk]
    · have hne_none : (some (Sum.inl k) : CompK hf.tm.K hg.tm.K) ≠ none := by simp
      have hne : (some (Sum.inl k) : CompK hf.tm.K hg.tm.K) ≠ some (Sum.inl hf.tm.k₁) := by simp [hk]
      rw [Function.update_of_ne hne_none, Function.update_of_ne hne]
      simp [bridgeStk, hk]
  · simp [bridgeStk]

theorem bridge_step_copy_nil {β : Type} {eb : Computability.FinEncoding β}
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g)
    (s2 : List (hg.tm.Γ hg.tm.k₀)) :
    (compTM hf hg).step (bridgeCfg hf hg (some (Sum.inr true)) [] [] s2) =
      some (bridgeCfg hf hg (some (Sum.inl (Sum.inr hg.tm.main))) [] [] s2) := by
  dsimp [FinTM2.step, Turing.TM2.step, compTM, bridgeCfg, bridgeCopyStmt, Turing.TM2.stepAux]
  have hhead : (bridgeStk hf hg [] [] s2 none).head? = none := rfl
  rw [hhead]
  dsimp [Option.isSome, cond]
  refine congrArg some (bridgeCfg_ext hf hg (fun idx => ?_))
  rcases idx with _ | ⟨k | k⟩ <;> simp [bridgeStk]

theorem bridge_step_copy_cons {β : Type} {eb : Computability.FinEncoding β}
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g)
    (b : Bool) (smid : List Bool) (s2 : List (hg.tm.Γ hg.tm.k₀)) :
    (compTM hf hg).step (bridgeCfg hf hg (some (Sum.inr true)) [] (b :: smid) s2) =
      some (bridgeCfg hf hg (some (Sum.inr true)) [] smid (hg.inputAlphabet.invFun b :: s2)) := by
  dsimp [FinTM2.step, Turing.TM2.step, compTM, bridgeCfg, bridgeCopyStmt, Turing.TM2.stepAux]
  have hhead : (bridgeStk hf hg [] (b :: smid) s2 none).head? = some b := rfl
  rw [hhead]
  dsimp [Option.isSome, Option.getD, cond]
  refine congrArg some (bridgeCfg_ext hf hg (fun idx => ?_))
  rcases idx with _ | ⟨k | k⟩
  · simp [bridgeStk]
  · simp [bridgeStk]
  · by_cases hk : k = hg.tm.k₀
    · subst hk
      rw [Function.update_self]
      simp [bridgeStk]
    · have hne : (some (Sum.inr k) : CompK hf.tm.K hg.tm.K) ≠ some (Sum.inr hg.tm.k₀) := by simp [hk]
      have hne_none : (some (Sum.inr k) : CompK hf.tm.K hg.tm.K) ≠ none := by simp
      rw [Function.update_of_ne hne, Function.update_of_ne hne_none]
      simp [bridgeStk, hk]

def bridge_rev_evals {β : Type} {eb : Computability.FinEncoding β}
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g) :
    ∀ (y smid : List Bool),
      Turing.EvalsToInTime (compTM hf hg).step
        (bridgeCfg hf hg (some (Sum.inr false)) (List.map (⇑hf.outputAlphabet.symm) y) smid [])
        (some (bridgeCfg hf hg (some (Sum.inr true)) [] (y.reverse ++ smid) []))
        (y.length + 1)
  | [], smid => by
    simpa using evalsInOne (bridge_step_rev_nil hf hg smid)
  | b :: y, smid => by
    have hstep := bridge_step_rev_cons hf hg (hf.outputAlphabet.symm b) (List.map (⇑hf.outputAlphabet.symm) y) smid
    have heq : hf.outputAlphabet.toFun (hf.outputAlphabet.symm b) = b := hf.outputAlphabet.apply_symm_apply b
    rw [heq] at hstep
    have ih := bridge_rev_evals hf hg y (b :: smid)
    have h := evalsTrans (evalsInOne hstep) ih
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact evalsMono h (by simp)

def bridge_copy_evals {β : Type} {eb : Computability.FinEncoding β}
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g) :
    ∀ (smid : List Bool) (s2 : List (hg.tm.Γ hg.tm.k₀)),
      Turing.EvalsToInTime (compTM hf hg).step
        (bridgeCfg hf hg (some (Sum.inr true)) [] smid s2)
        (some (bridgeCfg hf hg (some (Sum.inl (Sum.inr hg.tm.main))) [] []
          ((List.map (⇑hg.inputAlphabet.symm) smid).reverse ++ s2)))
        (smid.length + 1)
  | [], s2 => by
    simpa using evalsInOne (bridge_step_copy_nil hf hg s2)
  | b :: smid, s2 => by
    have hstep := bridge_step_copy_cons hf hg b smid s2
    have ih := bridge_copy_evals hf hg smid (hg.inputAlphabet.invFun b :: s2)
    have h := evalsTrans (evalsInOne hstep) ih
    dsimp [List.map]
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact evalsMono h (by simp)

theorem initList_compTM_eq {β : Type} {eb : Computability.FinEncoding β}
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g)
    (s : List (hf.tm.Γ hf.tm.k₀)) :
    Turing.initList (compTM hf hg) s = embedCfg₁ hf hg (Turing.initList hf.tm s) := by
  unfold Turing.initList embedCfg₁ embedOptΛ₁ compTM
  congr 1
  funext idx
  rcases idx with _ | ⟨k | k⟩
  · simp [embedStk₁]
  · by_cases hk : k = hf.tm.k₀
    · subst hk; simp [embedStk₁]
    · have hne : (some (Sum.inl k) : CompK hf.tm.K hg.tm.K) ≠ some (Sum.inl hf.tm.k₀) := by simp [hk]
      simp [embedStk₁, hk, hne]
  · simp [embedStk₁]

theorem embedCfg₁_haltList_eq {β : Type} {eb : Computability.FinEncoding β}
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g)
    (s : List (hf.tm.Γ hf.tm.k₁)) :
    embedCfg₁ hf hg (Turing.haltList hf.tm s) = bridgeCfg hf hg (some (Sum.inr false)) s [] [] := by
  unfold embedCfg₁ Turing.haltList bridgeCfg embedOptΛ₁
  congr 1
  funext idx
  rcases idx with _ | ⟨k | k⟩
  · simp [embedStk₁, bridgeStk]
  · simp [embedStk₁, bridgeStk]
  · by_cases hk : k = hg.tm.k₀
    · subst hk; simp [embedStk₁, bridgeStk]
    · simp [embedStk₁, bridgeStk, hk]

theorem bridgeCfg_eq_embedCfg₂_initList {β : Type} {eb : Computability.FinEncoding β}
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g)
    (s : List (hg.tm.Γ hg.tm.k₀)) :
    bridgeCfg hf hg (some (Sum.inl (Sum.inr hg.tm.main))) [] [] s =
      embedCfg₂ hf hg (Turing.initList hg.tm s) := by
  unfold bridgeCfg embedCfg₂ Turing.initList embedOptΛ₂
  congr 1
  funext idx
  rcases idx with _ | ⟨k | k⟩
  · simp [bridgeStk, embedStk₂]
  · by_cases hk : k = hf.tm.k₁
    · subst hk; simp [bridgeStk, embedStk₂]
    · simp [bridgeStk, embedStk₂, hk]
  · simp [bridgeStk, embedStk₂]

theorem embedCfg₂_haltList_eq {β : Type} {eb : Computability.FinEncoding β}
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g)
    (s : List (hg.tm.Γ hg.tm.k₁)) :
    embedCfg₂ hf hg (Turing.haltList hg.tm s) = Turing.haltList (compTM hf hg) s := by
  unfold embedCfg₂ Turing.haltList embedOptΛ₂ compTM
  congr 1
  funext idx
  rcases idx with _ | ⟨k | k⟩
  · simp [embedStk₂]
  · simp [embedStk₂]
  · by_cases hk : k = hg.tm.k₁
    · subst hk; simp [embedStk₂]
    · have hne : (some (Sum.inr k) : CompK hf.tm.K hg.tm.K) ≠ some (Sum.inr hg.tm.k₁) := by simp [hk]
      simp [embedStk₂, hk, hne]

noncomputable def compTM2ComputableInPolyTime {β : Type} (eb : Computability.FinEncoding β)
    {f : BitString → BitString} {g : BitString → β}
    (hf : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f)
    (hg : Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb g) :
    Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString eb (fun x => g (f x)) :=
  let pOut : Polynomial ℕ := Polynomial.X + hf.time * Polynomial.C (tmMaxPush hf.tm)
  { tm := compTM hf hg
    inputAlphabet := hf.inputAlphabet
    outputAlphabet := hg.outputAlphabet
    time := (hg.time.comp pOut + (Polynomial.C 2 * pOut + Polynomial.C 2)) + hf.time
    outputsFun := fun x => by
      dsimp [Turing.TM2OutputsInTime]
      have h1 : Turing.EvalsToInTime (compTM hf hg).step
          (Turing.initList (compTM hf hg) (List.map (⇑hf.inputAlphabet.symm) (ComplexitySAT.finEncodingBitString.encode x)))
          (some (bridgeCfg hf hg (some (Sum.inr false)) (List.map (⇑hf.outputAlphabet.symm) (f x)) [] []))
          (hf.time.eval (ComplexitySAT.finEncodingBitString.encode x).length) := by
        rw [initList_compTM_eq hf hg, ← embedCfg₁_haltList_eq hf hg]
        exact compTM_evals_phase1 hf hg (hf.outputsFun x)
      have h2a := bridge_rev_evals hf hg (f x) []
      rw [List.append_nil] at h2a
      have h2b := bridge_copy_evals hf hg (f x).reverse []
      rw [List.append_nil, List.length_reverse, ← List.map_reverse, List.reverse_reverse] at h2b
      have h2 := evalsTrans h2a h2b
      rw [bridgeCfg_eq_embedCfg₂_initList hf hg] at h2
      have h3 : Turing.EvalsToInTime (compTM hf hg).step
          (embedCfg₂ hf hg (Turing.initList hg.tm (List.map (⇑hg.inputAlphabet.symm) (f x))))
          (some (Turing.haltList (compTM hf hg) (List.map (⇑hg.outputAlphabet.symm) (eb.encode (g (f x))))))
          (hg.time.eval (f x).length) := by
        rw [← embedCfg₂_haltList_eq hf hg]
        exact compTM_evals_phase3 hf hg (hg.outputsFun (f x))
      have h12 := evalsTrans h1 h2
      have h123 := evalsTrans h12 h3
      refine evalsMono h123 ?_
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
      have hfx_le : (f x).length ≤ pOut.eval x.length := by
        dsimp [pOut]
        simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
        omega
      have hg_mono : hg.time.eval (f x).length ≤ (hg.time.comp pOut).eval x.length := by
        rw [Polynomial.eval_comp]
        exact polyEvalMono hg.time (f x).length (pOut.eval x.length) hfx_le
      dsimp [ComplexitySAT.finEncodingBitString]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      omega }

theorem tm2_comp_bitstring_poly :
    ∀ (f g : ComplexitySAT.BitString → ComplexitySAT.BitString),
      Nonempty (Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f) →
      Nonempty (Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString g) →
      Nonempty (Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString (fun x => g (f x))) := by
  rintro f g ⟨hf⟩ ⟨hg⟩
  exact ⟨compTM2ComputableInPolyTime ComplexitySAT.finEncodingBitString hf hg⟩

def PolyManyOneReduces (L K : ComplexitySAT.Language) : Prop :=
  ∃ f : ComplexitySAT.BitString → ComplexitySAT.BitString,
    Nonempty (TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f) ∧
    ∀ x, L x ↔ K (f x)

theorem reduction_preserves_P_sub2 :
    ∀ (f : ComplexitySAT.BitString → ComplexitySAT.BitString) (K : ComplexitySAT.Language),
      Nonempty (Turing.TM2ComputableInPolyTime ComplexitySAT.finEncodingBitString ComplexitySAT.finEncodingBitString f) →
      ComplexitySAT.InP K → ComplexitySAT.InP (fun x => K (f x)) := by
  rintro f K ⟨hf⟩ ⟨decideK, ⟨hK⟩, hcorr⟩
  exact ⟨fun x => decideK (f x), ⟨compTM2ComputableInPolyTime Computability.finEncodingBoolBool hf hK⟩, fun x => hcorr (f x)⟩

theorem reduction_preserves_P {L K : Language} (h : PolyManyOneReduces L K)
    (hK : InP K) : InP L := by
  obtain ⟨f, hf, hiff⟩ := h
  obtain ⟨D, hD, hspec⟩ := reduction_preserves_P_sub2 f K hf hK
  exact ⟨D, hD, fun x => (hiff x).trans (hspec x)⟩

end ComplexitySAT
