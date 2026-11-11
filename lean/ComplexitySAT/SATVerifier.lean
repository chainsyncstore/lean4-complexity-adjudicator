import ComplexitySAT.CNF
import ComplexitySAT.MachineBounds

/-! A five-stack CNF verifier with a linear step bound in the length of the paired input. -/

set_option autoImplicit false
set_option linter.constructorNameAsVariable false
set_option linter.unnecessarySimpa false

namespace ComplexitySAT

open Turing Computability Polynomial Turing.TM2.Stmt

def walkWitness : Nat → BitString → BitString → BitString × BitString
  | 0, w, wbak => (w, wbak)
  | v + 1, [], wbak => walkWitness v [] wbak
  | v + 1, b :: ws, wbak => walkWitness v ws (b :: wbak)

def restoreWitness : BitString → BitString → BitString
  | w, [] => w
  | w, b :: wbak => restoreWitness (b :: w) wbak

theorem walkWitness_eq (v : Nat) (w wbak : BitString) :
    walkWitness v w wbak = (w.drop v, (w.take v).reverse ++ wbak) := by
  induction v generalizing w wbak with
  | zero => simp [walkWitness]
  | succ v ih =>
    cases w with
    | nil =>
      rw [walkWitness, ih [] wbak]
      simp
    | cons b ws =>
      rw [walkWitness, ih ws (b :: wbak)]
      simp [List.take_succ_cons, List.drop_succ_cons, List.append_assoc]

theorem restoreWitness_eq (w wbak : BitString) :
    restoreWitness w wbak = wbak.reverse ++ w := by
  induction wbak generalizing w with
  | nil => simp [restoreWitness]
  | cons b rest ih =>
    rw [restoreWitness, ih (b :: w)]
    simp [List.append_assoc]

theorem drop_head_getD_eq (v : Nat) (w : BitString) :
    (w.drop v).head?.getD false = w.getD v false := by
  induction v generalizing w with
  | zero =>
    cases w <;> rfl
  | succ v ih =>
    cases w with
    | nil => simp [List.getD]
    | cons b ws =>
      simpa [List.drop_succ_cons, List.getD] using ih ws

theorem walk_restore_witness_exact (v : Nat) (w : BitString) :
    (walkWitness v w []).1.head?.getD false = w.getD v false ∧
    restoreWitness (walkWitness v w []).1 (walkWitness v w []).2 = w ∧
    (walkWitness v w []).2.length ≤ v := by
  rw [walkWitness_eq, List.append_nil, restoreWitness_eq]
  refine ⟨drop_head_getD_eq v w, ?_, ?_⟩
  · simp [List.reverse_reverse, List.take_append_drop]
  · simp [List.length_take]

-- Part 2: Streaming CNF Evaluator & Exact Equivalence with satVerifierBool

def streamLits (w : BitString) (clauseSat : Bool) : Nat → BitString → Option (Bool × BitString)
  | 0, sx => some (clauseSat, sx)
  | k + 1, sx =>
    match parseUnary sx with
    | some (v, pol :: rest) =>
      let wv := (walkWitness v w []).1.head?.getD false
      streamLits w (clauseSat || (wv == pol)) k rest
    | _ => none

def streamClauses (w : BitString) (allSat : Bool) : Nat → BitString → Option (Bool × BitString)
  | 0, sx => some (allSat, sx)
  | m + 1, sx =>
    match parseUnary sx with
    | some (k, s1) =>
      match streamLits w false k s1 with
      | some (cSat, s2) => streamClauses w (allSat && cSat) m s2
      | none => none
    | none => none

def satVerifierStream (u : BitString) : Bool :=
  let x := pairDecodeFirst u
  let w := pairDecodeSecond u
  match parseUnary x with
  | some (m, s1) =>
    match streamClauses w true m s1 with
    | some (res, []) => res
    | _ => false
  | none => false

theorem evalLiteral_eq_beq (w : BitString) (v : Nat) (pol : Bool) :
    evalLiteral w (v, pol) = (w.getD v false == pol) := by
  unfold evalLiteral
  cases w.getD v false <;> cases pol <;> rfl

theorem streamLits_eq (w : BitString) :
    ∀ (k : Nat) (clauseSat : Bool) (sx : BitString),
      streamLits w clauseSat k sx =
        match parseMany parseLiteral k sx with
        | some (c, rest) => some (clauseSat || evalClause w c, rest)
        | none => none
  | 0, clauseSat, sx => by
    simp [streamLits, parseMany, evalClause]
  | k + 1, clauseSat, sx => by
    rw [streamLits, parseMany]
    have hpl : parseLiteral sx =
        match parseUnary sx with
        | some (v, b :: rest) => some ((v, b), rest)
        | _ => none := rfl
    rw [hpl]
    cases hp : parseUnary sx with
    | none => rfl
    | some pr =>
      rcases pr with ⟨v, r⟩
      cases r with
      | nil => rfl
      | cons pol rest =>
        dsimp only
        rw [(walk_restore_witness_exact v w).1]
        rw [streamLits_eq w k (clauseSat || (w.getD v false == pol)) rest]
        cases hm : parseMany parseLiteral k rest with
        | none => rfl
        | some pr2 =>
          rcases pr2 with ⟨cs, s2⟩
          simp only [evalClause, List.any_cons, Bool.or_assoc, evalLiteral_eq_beq]

theorem streamClauses_eq (w : BitString) :
    ∀ (m : Nat) (allSat : Bool) (sx : BitString),
      streamClauses w allSat m sx =
        match parseMany parseClause m sx with
        | some (f, rest) => some (allSat && evalCNF w f, rest)
        | none => none
  | 0, allSat, sx => by
    simp [streamClauses, parseMany, evalCNF]
  | m + 1, allSat, sx => by
    rw [streamClauses, parseMany]
    have hpc : parseClause sx =
        match parseUnary sx with
        | some (k, s1) => parseMany parseLiteral k s1
        | none => none := rfl
    rw [hpc]
    cases hp : parseUnary sx with
    | none => rfl
    | some pr =>
      rcases pr with ⟨k, s1⟩
      dsimp only
      rw [streamLits_eq w k false s1]
      cases hl : parseMany parseLiteral k s1 with
      | none => rfl
      | some pr2 =>
        rcases pr2 with ⟨c, s2⟩
        dsimp only
        rw [Bool.false_or, streamClauses_eq w m (allSat && evalClause w c) s2]
        cases hc : parseMany parseClause m s2 with
        | none => rfl
        | some pr3 =>
          rcases pr3 with ⟨fs, s3⟩
          simp only [evalCNF, List.all_cons, Bool.and_assoc]

theorem satVerifierStream_eq (u : BitString) :
    satVerifierStream u = satVerifierBool u := by
  unfold satVerifierStream satVerifierBool cnfDecode
  dsimp only
  cases hp : parseUnary (pairDecodeFirst u) with
  | none => rfl
  | some pr =>
    rcases pr with ⟨m, s1⟩
    dsimp only
    rw [streamClauses_eq (pairDecodeSecond u) m true s1]
    cases hc : parseMany parseClause m s1 with
    | none => rfl
    | some pr2 =>
      rcases pr2 with ⟨f, r⟩
      cases r with
      | nil => simp [Bool.true_and]
      | cons _ _ => rfl

-- Part 3: 5-Stack Bool-Alphabet FinTM2 (satVerifierTM) Computing satVerifierBool in Linear Time

theorem parseUnary_rest_length_eq {sx rest : BitString} {n : Nat}
    (h : parseUnary sx = some (n, rest)) :
    sx.length = n + 1 + rest.length := by
  have hs : sx = unaryNat n ++ rest := (parseUnary_exact sx rest n).mp h
  rw [hs, List.length_append]
  simp [unaryNat]

theorem streamLits_rest_le (w : BitString) :
    ∀ (k : Nat) (clauseSat : Bool) (sx rest : BitString) (cSat : Bool),
      streamLits w clauseSat k sx = some (cSat, rest) → rest.length ≤ sx.length
  | 0, clauseSat, sx, rest, cSat, h => by
    simp only [streamLits, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩
    exact le_rfl
  | k + 1, clauseSat, sx, rest, cSat, h => by
    unfold streamLits at h
    cases hp : parseUnary sx with
    | none => rw [hp] at h; cases h
    | some pr =>
      rcases pr with ⟨v, r⟩
      rw [hp] at h
      cases r with
      | nil => cases h
      | cons pol s1 =>
        dsimp only at h
        have hlen := parseUnary_rest_length_eq hp
        simp only [List.length_cons] at hlen
        have ih := streamLits_rest_le w k (clauseSat || ((walkWitness v w []).1.head?.getD false == pol)) s1 rest cSat h
        omega

theorem streamClauses_rest_le (w : BitString) :
    ∀ (m : Nat) (allSat : Bool) (sx rest : BitString) (res : Bool),
      streamClauses w allSat m sx = some (res, rest) → rest.length ≤ sx.length
  | 0, allSat, sx, rest, res, h => by
    simp only [streamClauses, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩
    exact le_rfl
  | m + 1, allSat, sx, rest, res, h => by
    unfold streamClauses at h
    cases hp : parseUnary sx with
    | none => rw [hp] at h; cases h
    | some pr =>
      rcases pr with ⟨k, s1⟩
      rw [hp] at h
      dsimp only at h
      have hlen1 := parseUnary_rest_length_eq hp
      cases hl : streamLits w false k s1 with
      | none => rw [hl] at h; cases h
      | some pr2 =>
        rcases pr2 with ⟨cSat, s2⟩
        rw [hl] at h
        dsimp only at h
        have hlen2 := streamLits_rest_le w k false s1 s2 cSat hl
        have ih := streamClauses_rest_le w m (allSat && cSat) s2 rest res h
        omega

inductive SVStack where
  | w | wbak | x | m | k
  deriving DecidableEq, Repr

instance : Fintype SVStack where
  elems := {.w, .wbak, .x, .m, .k}
  complete := by intro s; cases s <;> decide

inductive SVLabel where
  | splitScan : SVLabel
  | splitRev : SVLabel
  | readClauseCount : SVLabel
  | nextClause : Bool → SVLabel
  | readLitCount : Bool → SVLabel
  | nextLit : Bool → Bool → SVLabel
  | walkLit : Bool → Bool → SVLabel
  | restoreW : Bool → Bool → SVLabel
  | finish : Bool → SVLabel
  deriving DecidableEq, Repr

instance : Fintype SVLabel where
  elems := {
    .splitScan, .splitRev, .readClauseCount,
    .nextClause false, .nextClause true,
    .readLitCount false, .readLitCount true,
    .nextLit false false, .nextLit false true, .nextLit true false, .nextLit true true,
    .walkLit false false, .walkLit false true, .walkLit true false, .walkLit true true,
    .restoreW false false, .restoreW false true, .restoreW true false, .restoreW true true,
    .finish false, .finish true
  }
  complete := by
    intro l
    cases l with
    | splitScan => decide
    | splitRev => decide
    | readClauseCount => decide
    | nextClause a => cases a <;> decide
    | readLitCount a => cases a <;> decide
    | nextLit a c => cases a <;> cases c <;> decide
    | walkLit a c => cases a <;> cases c <;> decide
    | restoreW a c => cases a <;> cases c <;> decide
    | finish r => cases r <;> decide

def satVerifierTM : FinTM2 where
  K := SVStack
  k₀ := .w
  k₁ := .w
  Γ _ := Bool
  Λ := SVLabel
  main := .splitScan
  σ := Option Bool × Option Bool
  initialState := (none, none)
  Γk₀Fin := inferInstance
  m
    | .splitScan =>
      pop .w (fun _ top1 => (top1, none))
        (branch (fun s => s.1 == some false)
          (pop .w (fun s top2 => (s.1, top2))
            (branch (fun s => s.2.isSome)
              (push .wbak (fun s => s.2.getD false)
                (load (fun _ => (none, none)) (goto (fun _ => .splitScan))))
              (load (fun _ => (none, none)) (goto (fun _ => .splitRev)))))
          (load (fun _ => (none, none)) (goto (fun _ => .splitRev))))
    | .splitRev =>
      pop .wbak (fun _ top1 => (top1, none))
        (branch (fun s => s.1.isSome)
          (push .x (fun s => s.1.getD false)
            (load (fun _ => (none, none)) (goto (fun _ => .splitRev))))
          (load (fun _ => (none, none)) (goto (fun _ => .readClauseCount))))
    | .readClauseCount =>
      pop .x (fun _ top => (top, none))
        (branch (fun s => s.1 == some false)
          (push .m (fun _ => false)
            (load (fun _ => (none, none)) (goto (fun _ => .readClauseCount))))
          (branch (fun s => s.1 == some true)
            (load (fun _ => (none, none)) (goto (fun _ => .nextClause true)))
            (load (fun _ => (none, none)) (goto (fun _ => .finish false)))))
    | .nextClause allSat =>
      pop .m (fun _ top1 => (top1, none))
        (branch (fun s => s.1.isSome)
          (load (fun _ => (none, none)) (goto (fun _ => .readLitCount allSat)))
          (pop .x (fun _ top2 => (none, top2))
            (branch (fun s => s.2.isSome)
              (load (fun _ => (none, none)) (goto (fun _ => .finish false)))
              (load (fun _ => (none, none)) (goto (fun _ => .finish allSat))))))
    | .readLitCount allSat =>
      pop .x (fun _ top => (top, none))
        (branch (fun s => s.1 == some false)
          (push .k (fun _ => false)
            (load (fun _ => (none, none)) (goto (fun _ => .readLitCount allSat))))
          (branch (fun s => s.1 == some true)
            (load (fun _ => (none, none)) (goto (fun _ => .nextLit allSat false)))
            (load (fun _ => (none, none)) (goto (fun _ => .finish false)))))
    | .nextLit allSat clauseSat =>
      pop .k (fun _ top => (top, none))
        (branch (fun s => s.1.isSome)
          (load (fun _ => (none, none)) (goto (fun _ => .walkLit allSat clauseSat)))
          (load (fun _ => (none, none)) (goto (fun _ => .nextClause (allSat && clauseSat)))))
    | .walkLit allSat clauseSat =>
      pop .x (fun _ top1 => (top1, none))
        (branch (fun s => s.1 == some false)
          (pop .w (fun s top2 => (s.1, top2))
            (branch (fun s => s.2.isSome)
              (push .wbak (fun s => s.2.getD false)
                (load (fun _ => (none, none)) (goto (fun _ => .walkLit allSat clauseSat))))
              (load (fun _ => (none, none)) (goto (fun _ => .walkLit allSat clauseSat)))))
          (branch (fun s => s.1 == some true)
            (pop .x (fun _ top1 => (top1, none))
              (branch (fun s => s.1.isSome)
                (peek .w (fun s top2 => (s.1, top2))
                  (branch (fun s => s.2.getD false == s.1.getD false)
                    (load (fun _ => (none, none)) (goto (fun _ => .restoreW allSat true)))
                    (load (fun _ => (none, none)) (goto (fun _ => .restoreW allSat clauseSat)))))
                (load (fun _ => (none, none)) (goto (fun _ => .finish false)))))
            (load (fun _ => (none, none)) (goto (fun _ => .finish false)))))
    | .restoreW allSat clauseSat =>
      pop .wbak (fun _ top => (top, none))
        (branch (fun s => s.1.isSome)
          (push .w (fun s => s.1.getD false)
            (load (fun _ => (none, none)) (goto (fun _ => .restoreW allSat clauseSat))))
          (load (fun _ => (none, none)) (goto (fun _ => .nextLit allSat clauseSat))))
    | .finish res =>
      pop .w (fun _ top => (top, none))
        (branch (fun s => s.1.isSome)
          (load (fun _ => (none, none)) (goto (fun _ => .finish res)))
          (pop .wbak (fun _ top => (top, none))
            (branch (fun s => s.1.isSome)
              (load (fun _ => (none, none)) (goto (fun _ => .finish res)))
              (pop .x (fun _ top => (top, none))
                (branch (fun s => s.1.isSome)
                  (load (fun _ => (none, none)) (goto (fun _ => .finish res)))
                  (pop .m (fun _ top => (top, none))
                    (branch (fun s => s.1.isSome)
                      (load (fun _ => (none, none)) (goto (fun _ => .finish res)))
                      (pop .k (fun _ top => (top, none))
                        (branch (fun s => s.1.isSome)
                          (load (fun _ => (none, none)) (goto (fun _ => .finish res)))
                          (push .w (fun _ => res)
                            (load (fun _ => (none, none)) halt)))))))))))

def svCfg (l : Option SVLabel) (sw swbak sx sm sk : List Bool) : satVerifierTM.Cfg :=
  { l := l
    var := (none, none)
    stk := fun k => match k with
      | .w => sw
      | .wbak => swbak
      | .x => sx
      | .m => sm
      | .k => sk }

theorem svCfg_ext {l : Option SVLabel} {sw swbak sx sm sk : List Bool} {stk : SVStack → List Bool}
    (h : ∀ k : SVStack, stk k = (svCfg l sw swbak sx sm sk).stk k) :
    (⟨l, (none, none), stk⟩ : satVerifierTM.Cfg) = svCfg l sw swbak sx sm sk := by
  unfold svCfg
  congr 1
  funext k
  exact h k

theorem svCfg_init (u : List Bool) :
    Turing.initList satVerifierTM u = svCfg (some .splitScan) u [] [] [] [] := by
  unfold Turing.initList svCfg
  congr 1
  funext k
  cases k <;> rfl

theorem svCfg_halt (res : Bool) :
    Turing.haltList satVerifierTM [res] = svCfg none [res] [] [] [] [] := by
  unfold Turing.haltList svCfg
  congr 1
  funext k
  cases k <;> rfl

theorem replicate_false_append_cons (n : Nat) (xs : List Bool) :
    List.replicate n false ++ (false :: xs) = false :: (List.replicate n false ++ xs) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

-- Finish drain lemmas

theorem sv_step_finish_w (res b : Bool) (sw swbak sx sm sk : List Bool) :
    satVerifierTM.step (svCfg (some (.finish res)) (b :: sw) swbak sx sm sk) =
      some (svCfg (some (.finish res)) sw swbak sx sm sk) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

theorem sv_step_finish_wbak (res b : Bool) (swbak sx sm sk : List Bool) :
    satVerifierTM.step (svCfg (some (.finish res)) [] (b :: swbak) sx sm sk) =
      some (svCfg (some (.finish res)) [] swbak sx sm sk) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

theorem sv_step_finish_x (res b : Bool) (sx sm sk : List Bool) :
    satVerifierTM.step (svCfg (some (.finish res)) [] [] (b :: sx) sm sk) =
      some (svCfg (some (.finish res)) [] [] sx sm sk) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

theorem sv_step_finish_m (res b : Bool) (sm sk : List Bool) :
    satVerifierTM.step (svCfg (some (.finish res)) [] [] [] (b :: sm) sk) =
      some (svCfg (some (.finish res)) [] [] [] sm sk) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

theorem sv_step_finish_k (res b : Bool) (sk : List Bool) :
    satVerifierTM.step (svCfg (some (.finish res)) [] [] [] [] (b :: sk)) =
      some (svCfg (some (.finish res)) [] [] [] [] sk) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

theorem sv_step_finish_nil (res : Bool) :
    satVerifierTM.step (svCfg (some (.finish res)) [] [] [] [] []) =
      some (Turing.haltList satVerifierTM [res]) := by
  rw [svCfg_halt]
  exact congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

def sv_finish_k_evals (res : Bool) : ∀ (sk : List Bool),
    Turing.EvalsToInTime satVerifierTM.step
      (svCfg (some (.finish res)) [] [] [] [] sk)
      (some (Turing.haltList satVerifierTM [res]))
      (sk.length + 1)
  | [] => evalsInOne (sv_step_finish_nil res)
  | b :: sk =>
    evalsMono (evalsTrans (evalsInOne (sv_step_finish_k res b sk)) (sv_finish_k_evals res sk)) (by simp)

def sv_finish_m_evals (res : Bool) : ∀ (sm sk : List Bool),
    Turing.EvalsToInTime satVerifierTM.step
      (svCfg (some (.finish res)) [] [] [] sm sk)
      (some (Turing.haltList satVerifierTM [res]))
      (sm.length + sk.length + 1)
  | [], sk => by simpa using sv_finish_k_evals res sk
  | b :: sm, sk =>
    evalsMono (evalsTrans (evalsInOne (sv_step_finish_m res b sm sk)) (sv_finish_m_evals res sm sk)) (by simp; omega)

def sv_finish_x_evals (res : Bool) : ∀ (sx sm sk : List Bool),
    Turing.EvalsToInTime satVerifierTM.step
      (svCfg (some (.finish res)) [] [] sx sm sk)
      (some (Turing.haltList satVerifierTM [res]))
      (sx.length + sm.length + sk.length + 1)
  | [], sm, sk => by simpa using sv_finish_m_evals res sm sk
  | b :: sx, sm, sk =>
    evalsMono (evalsTrans (evalsInOne (sv_step_finish_x res b sx sm sk)) (sv_finish_x_evals res sx sm sk)) (by simp; omega)

def sv_finish_wbak_evals (res : Bool) : ∀ (swbak sx sm sk : List Bool),
    Turing.EvalsToInTime satVerifierTM.step
      (svCfg (some (.finish res)) [] swbak sx sm sk)
      (some (Turing.haltList satVerifierTM [res]))
      (swbak.length + sx.length + sm.length + sk.length + 1)
  | [], sx, sm, sk => by simpa using sv_finish_x_evals res sx sm sk
  | b :: swbak, sx, sm, sk =>
    evalsMono (evalsTrans (evalsInOne (sv_step_finish_wbak res b swbak sx sm sk)) (sv_finish_wbak_evals res swbak sx sm sk)) (by simp; omega)

def sv_finish_evals (res : Bool) : ∀ (sw swbak sx sm sk : List Bool),
    Turing.EvalsToInTime satVerifierTM.step
      (svCfg (some (.finish res)) sw swbak sx sm sk)
      (some (Turing.haltList satVerifierTM [res]))
      (sw.length + swbak.length + sx.length + sm.length + sk.length + 1)
  | [], swbak, sx, sm, sk => by simpa using sv_finish_wbak_evals res swbak sx sm sk
  | b :: sw, swbak, sx, sm, sk =>
    evalsMono (evalsTrans (evalsInOne (sv_step_finish_w res b sw swbak sx sm sk)) (sv_finish_evals res sw swbak sx sm sk)) (by simp; omega)

theorem eq_replicate_false_of_parseUnary_none :
    ∀ (sx : BitString), parseUnary sx = none → sx = List.replicate sx.length false
  | [], _ => rfl
  | true :: _, h => by simp [parseUnary] at h
  | false :: rest, h => by
    unfold parseUnary at h
    cases hp : parseUnary rest with
    | none =>
      simp only [List.length_cons, List.replicate_succ, List.cons.injEq, true_and]
      exact eq_replicate_false_of_parseUnary_none rest hp
    | some pr => rw [hp] at h; cases h

theorem walkWitness_length_sum (v : Nat) (sw swbak : BitString) :
    (walkWitness v sw swbak).1.length + (walkWitness v sw swbak).2.length =
      sw.length + swbak.length := by
  rw [walkWitness_eq]
  simp only [List.length_append, List.length_reverse, List.length_drop, List.length_take]
  omega

-- Step lemmas for splitScan and splitRev

theorem sv_step_splitScan_nil (acc : List Bool) :
    satVerifierTM.step (svCfg (some .splitScan) [] acc [] [] []) =
      some (svCfg (some .splitRev) [] acc [] [] []) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

theorem sv_step_splitScan_true (w acc : List Bool) :
    satVerifierTM.step (svCfg (some .splitScan) (true :: w) acc [] [] []) =
      some (svCfg (some .splitRev) w acc [] [] []) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

theorem sv_step_splitScan_false_nil (acc : List Bool) :
    satVerifierTM.step (svCfg (some .splitScan) [false] acc [] [] []) =
      some (svCfg (some .splitRev) [] acc [] [] []) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

theorem sv_step_splitScan_false_cons (b : Bool) (rest acc : List Bool) :
    satVerifierTM.step (svCfg (some .splitScan) (false :: b :: rest) acc [] [] []) =
      some (svCfg (some .splitScan) rest (b :: acc) [] [] []) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

def sv_splitScan_evals : ∀ (u acc : List Bool),
    Turing.EvalsToInTime satVerifierTM.step
      (svCfg (some .splitScan) u acc [] [] [])
      (some (svCfg (some .splitRev) (pairDecodeSecond u) ((pairDecodeFirst u).reverse ++ acc) [] [] []))
      (u.length + 1)
  | [], acc => by simpa [pairDecodeFirst, pairDecodeSecond] using evalsInOne (sv_step_splitScan_nil acc)
  | true :: w, acc => by
    dsimp [pairDecodeFirst, pairDecodeSecond]
    exact evalsMono (evalsInOne (sv_step_splitScan_true w acc)) (by simp)
  | [false], acc => by
    dsimp [pairDecodeFirst, pairDecodeSecond]
    exact evalsMono (evalsInOne (sv_step_splitScan_false_nil acc)) (by simp)
  | false :: b :: rest, acc => by
    dsimp [pairDecodeFirst, pairDecodeSecond]
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    have h := evalsTrans (evalsInOne (sv_step_splitScan_false_cons b rest acc)) (sv_splitScan_evals rest (b :: acc))
    exact evalsMono h (by simp)

theorem sv_step_splitRev_nil (w sx : List Bool) :
    satVerifierTM.step (svCfg (some .splitRev) w [] sx [] []) =
      some (svCfg (some .readClauseCount) w [] sx [] []) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

theorem sv_step_splitRev_cons (b : Bool) (w acc sx : List Bool) :
    satVerifierTM.step (svCfg (some .splitRev) w (b :: acc) sx [] []) =
      some (svCfg (some .splitRev) w acc (b :: sx) [] []) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

def sv_splitRev_evals : ∀ (acc w sx : List Bool),
    Turing.EvalsToInTime satVerifierTM.step
      (svCfg (some .splitRev) w acc sx [] [])
      (some (svCfg (some .readClauseCount) w [] (acc.reverse ++ sx) [] []))
      (acc.length + 1)
  | [], w, sx => by simpa using evalsInOne (sv_step_splitRev_nil w sx)
  | b :: acc, w, sx => by
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    have h := evalsTrans (evalsInOne (sv_step_splitRev_cons b w acc sx)) (sv_splitRev_evals acc w (b :: sx))
    exact evalsMono h (by simp)

-- Step lemmas for restoreW

theorem sv_step_restoreW_nil (allSat clauseSat : Bool) (sw sx sm sk : List Bool) :
    satVerifierTM.step (svCfg (some (.restoreW allSat clauseSat)) sw [] sx sm sk) =
      some (svCfg (some (.nextLit allSat clauseSat)) sw [] sx sm sk) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

theorem sv_step_restoreW_cons (allSat clauseSat b : Bool) (sw swbak sx sm sk : List Bool) :
    satVerifierTM.step (svCfg (some (.restoreW allSat clauseSat)) sw (b :: swbak) sx sm sk) =
      some (svCfg (some (.restoreW allSat clauseSat)) (b :: sw) swbak sx sm sk) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

def sv_restoreW_evals (allSat clauseSat : Bool) : ∀ (swbak sw sx sm sk : List Bool),
    Turing.EvalsToInTime satVerifierTM.step
      (svCfg (some (.restoreW allSat clauseSat)) sw swbak sx sm sk)
      (some (svCfg (some (.nextLit allSat clauseSat)) (restoreWitness sw swbak) [] sx sm sk))
      (swbak.length + 1)
  | [], sw, sx, sm, sk => by simpa [restoreWitness] using evalsInOne (sv_step_restoreW_nil allSat clauseSat sw sx sm sk)
  | b :: swbak, sw, sx, sm, sk => by
    dsimp [restoreWitness]
    have h := evalsTrans (evalsInOne (sv_step_restoreW_cons allSat clauseSat b sw swbak sx sm sk))
      (sv_restoreW_evals allSat clauseSat swbak (b :: sw) sx sm sk)
    exact evalsMono h (by simp)

-- Step lemmas for walkLit

theorem sv_step_walkLit_false_nil (allSat clauseSat : Bool) (swbak r sm sk : List Bool) :
    satVerifierTM.step (svCfg (some (.walkLit allSat clauseSat)) [] swbak (false :: r) sm sk) =
      some (svCfg (some (.walkLit allSat clauseSat)) [] swbak r sm sk) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

theorem sv_step_walkLit_false_cons (allSat clauseSat b : Bool) (sw swbak r sm sk : List Bool) :
    satVerifierTM.step (svCfg (some (.walkLit allSat clauseSat)) (b :: sw) swbak (false :: r) sm sk) =
      some (svCfg (some (.walkLit allSat clauseSat)) sw (b :: swbak) r sm sk) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

def sv_walkLit_rep (allSat clauseSat : Bool) : ∀ (v : Nat) (sw swbak r sm sk : List Bool),
    Turing.EvalsToInTime satVerifierTM.step
      (svCfg (some (.walkLit allSat clauseSat)) sw swbak (List.replicate v false ++ r) sm sk)
      (some (svCfg (some (.walkLit allSat clauseSat)) (walkWitness v sw swbak).1 (walkWitness v sw swbak).2 r sm sk))
      v
  | 0, sw, swbak, r, sm, sk => by
    simpa [walkWitness] using evalsRefl (svCfg (some (.walkLit allSat clauseSat)) sw swbak r sm sk)
  | v + 1, [], swbak, r, sm, sk => by
    simp only [List.replicate_succ, List.cons_append, walkWitness]
    have h := evalsTrans (evalsInOne (sv_step_walkLit_false_nil allSat clauseSat swbak (List.replicate v false ++ r) sm sk))
      (sv_walkLit_rep allSat clauseSat v [] swbak r sm sk)
    exact evalsMono h (by omega)
  | v + 1, b :: sw, swbak, r, sm, sk => by
    simp only [List.replicate_succ, List.cons_append, walkWitness]
    have h := evalsTrans (evalsInOne (sv_step_walkLit_false_cons allSat clauseSat b sw swbak (List.replicate v false ++ r) sm sk))
      (sv_walkLit_rep allSat clauseSat v sw (b :: swbak) r sm sk)
    exact evalsMono h (by omega)

theorem sv_step_walkLit_nil (allSat clauseSat : Bool) (sw swbak sm sk : List Bool) :
    satVerifierTM.step (svCfg (some (.walkLit allSat clauseSat)) sw swbak [] sm sk) =
      some (svCfg (some (.finish false)) sw swbak [] sm sk) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

theorem sv_step_walkLit_true_nil (allSat clauseSat : Bool) (sw swbak sm sk : List Bool) :
    satVerifierTM.step (svCfg (some (.walkLit allSat clauseSat)) sw swbak [true] sm sk) =
      some (svCfg (some (.finish false)) sw swbak [] sm sk) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

theorem sv_step_walkLit_true_cons (allSat clauseSat pol : Bool) (sw swbak rest sm sk : List Bool) :
    satVerifierTM.step (svCfg (some (.walkLit allSat clauseSat)) sw swbak (true :: pol :: rest) sm sk) =
      some (svCfg (some (.restoreW allSat (clauseSat || (sw.head?.getD false == pol)))) sw swbak rest sm sk) := by
  cases sw with
  | nil =>
    cases pol <;> cases clauseSat <;>
      exact congrArg some (svCfg_ext (fun k => by cases k <;> rfl))
  | cons b ws =>
    cases b <;> cases pol <;> cases clauseSat <;>
      exact congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

def sv_walkLit_some_evals (allSat clauseSat : Bool) (w sx rest sm sk : List Bool) (v : Nat) (pol : Bool)
    (hp : parseUnary sx = some (v, pol :: rest)) :
    Turing.EvalsToInTime satVerifierTM.step
      (svCfg (some (.walkLit allSat clauseSat)) w [] sx sm sk)
      (some (svCfg (some (.nextLit allSat (clauseSat || ((walkWitness v w []).1.head?.getD false == pol)))) w [] rest sm sk))
      (2 * (sx.length - rest.length)) := by
  have hsx : sx = List.replicate v false ++ (true :: pol :: rest) := by
    simpa [unaryNat, List.append_assoc] using (parseUnary_exact sx (pol :: rest) v).mp hp
  have hlen : sx.length = v + 2 + rest.length := by
    have h0 := parseUnary_rest_length_eq hp
    simp only [List.length_cons] at h0
    omega
  have h1 := sv_walkLit_rep allSat clauseSat v w [] (true :: pol :: rest) sm sk
  rw [← hsx] at h1
  have h2 := evalsInOne (sv_step_walkLit_true_cons allSat clauseSat pol (walkWitness v w []).1 (walkWitness v w []).2 rest sm sk)
  have h3 := sv_restoreW_evals allSat (clauseSat || ((walkWitness v w []).1.head?.getD false == pol))
    (walkWitness v w []).2 (walkWitness v w []).1 rest sm sk
  rw [(walk_restore_witness_exact v w).2.1] at h3
  have hwlen : (walkWitness v w []).2.length ≤ v := (walk_restore_witness_exact v w).2.2
  exact evalsMono (evalsTrans (evalsTrans h1 h2) h3) (by omega)

def sv_walkLit_none_evals (allSat clauseSat : Bool) (w sx sm sk : List Bool)
    (hnone : parseUnary sx = none) :
    Turing.EvalsToInTime satVerifierTM.step
      (svCfg (some (.walkLit allSat clauseSat)) w [] sx sm sk)
      (some (Turing.haltList satVerifierTM [false]))
      (2 * sx.length + w.length + sm.length + sk.length + 2) := by
  have hsx : sx = List.replicate sx.length false ++ [] := by
    rw [List.append_nil]
    exact eq_replicate_false_of_parseUnary_none sx hnone
  have h1 := sv_walkLit_rep allSat clauseSat sx.length w [] [] sm sk
  rw [← hsx] at h1
  have h2 := evalsInOne (sv_step_walkLit_nil allSat clauseSat (walkWitness sx.length w []).1 (walkWitness sx.length w []).2 sm sk)
  have h3 := sv_finish_evals false (walkWitness sx.length w []).1 (walkWitness sx.length w []).2 [] sm sk
  have hsum := walkWitness_length_sum sx.length w []
  simp only [List.length_nil] at hsum h3
  exact evalsMono (evalsTrans (evalsTrans h1 h2) h3) (by omega)

def sv_walkLit_short_evals (allSat clauseSat : Bool) (w sx sm sk : List Bool) (v : Nat)
    (hp : parseUnary sx = some (v, [])) :
    Turing.EvalsToInTime satVerifierTM.step
      (svCfg (some (.walkLit allSat clauseSat)) w [] sx sm sk)
      (some (Turing.haltList satVerifierTM [false]))
      (2 * sx.length + w.length + sm.length + sk.length + 2) := by
  have hsx : sx = List.replicate v false ++ [true] := by
    simpa [unaryNat] using (parseUnary_exact sx [] v).mp hp
  have hlen : sx.length = v + 1 := by
    simpa using parseUnary_rest_length_eq hp
  have h1 := sv_walkLit_rep allSat clauseSat v w [] [true] sm sk
  rw [← hsx] at h1
  have h2 := evalsInOne (sv_step_walkLit_true_nil allSat clauseSat (walkWitness v w []).1 (walkWitness v w []).2 sm sk)
  have h3 := sv_finish_evals false (walkWitness v w []).1 (walkWitness v w []).2 [] sm sk
  have hsum := walkWitness_length_sum v w []
  simp only [List.length_nil] at hsum h3
  exact evalsMono (evalsTrans (evalsTrans h1 h2) h3) (by omega)

-- Step and evaluation lemmas for nextLit

theorem sv_step_nextLit_nil (allSat clauseSat : Bool) (w sx sm : List Bool) :
    satVerifierTM.step (svCfg (some (.nextLit allSat clauseSat)) w [] sx sm []) =
      some (svCfg (some (.nextClause (allSat && clauseSat))) w [] sx sm []) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

theorem sv_step_nextLit_cons (allSat clauseSat b : Bool) (w sx sm sk : List Bool) :
    satVerifierTM.step (svCfg (some (.nextLit allSat clauseSat)) w [] sx sm (b :: sk)) =
      some (svCfg (some (.walkLit allSat clauseSat)) w [] sx sm sk) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

def sv_nextLit_some_evals (allSat : Bool) (w sm : List Bool) :
    ∀ (k : Nat) (clauseSat : Bool) (sx rest : List Bool) (cSat : Bool),
      streamLits w clauseSat k sx = some (cSat, rest) →
      Turing.EvalsToInTime satVerifierTM.step
        (svCfg (some (.nextLit allSat clauseSat)) w [] sx sm (List.replicate k false))
        (some (svCfg (some (.nextClause (allSat && cSat))) w [] rest sm []))
        (3 * (sx.length - rest.length) + k + 1)
  | 0, clauseSat, sx, rest, cSat, h => by
    simp only [streamLits, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simpa using evalsInOne (sv_step_nextLit_nil allSat clauseSat w sx sm)
  | k + 1, clauseSat, sx, rest, cSat, h => by
    unfold streamLits at h
    cases hp : parseUnary sx with
    | none => rw [hp] at h; cases h
    | some pr =>
      rcases pr with ⟨v, r⟩
      rw [hp] at h
      cases r with
      | nil => cases h
      | cons pol s1 =>
        dsimp only at h
        have hlen1 := parseUnary_rest_length_eq hp
        simp only [List.length_cons] at hlen1
        have hlen2 := streamLits_rest_le w k (clauseSat || ((walkWitness v w []).1.head?.getD false == pol)) s1 rest cSat h
        have hStep := evalsInOne (sv_step_nextLit_cons allSat clauseSat false w sx sm (List.replicate k false))
        have hWalk := sv_walkLit_some_evals allSat clauseSat w sx s1 sm (List.replicate k false) v pol hp
        have hIH := sv_nextLit_some_evals allSat w sm k (clauseSat || ((walkWitness v w []).1.head?.getD false == pol)) s1 rest cSat h
        exact evalsMono (evalsTrans (evalsTrans hStep hWalk) hIH) (by omega)

def sv_nextLit_none_evals (allSat : Bool) (w sm : List Bool) :
    ∀ (k : Nat) (clauseSat : Bool) (sx : List Bool),
      streamLits w clauseSat k sx = none →
      Turing.EvalsToInTime satVerifierTM.step
        (svCfg (some (.nextLit allSat clauseSat)) w [] sx sm (List.replicate k false))
        (some (Turing.haltList satVerifierTM [false]))
        (3 * sx.length + w.length + sm.length + k + 3)
  | 0, clauseSat, sx, h => by
    simp [streamLits] at h
  | k + 1, clauseSat, sx, h => by
    unfold streamLits at h
    have hStep := evalsInOne (sv_step_nextLit_cons allSat clauseSat false w sx sm (List.replicate k false))
    cases hp : parseUnary sx with
    | none =>
      have hWalk := sv_walkLit_none_evals allSat clauseSat w sx sm (List.replicate k false) hp
      simp only [List.length_replicate] at hWalk
      exact evalsMono (evalsTrans hStep hWalk) (by omega)
    | some pr =>
      rcases pr with ⟨v, r⟩
      rw [hp] at h
      cases r with
      | nil =>
        have hWalk := sv_walkLit_short_evals allSat clauseSat w sx sm (List.replicate k false) v hp
        simp only [List.length_replicate] at hWalk
        exact evalsMono (evalsTrans hStep hWalk) (by omega)
      | cons pol s1 =>
        dsimp only at h
        have hlen1 := parseUnary_rest_length_eq hp
        simp only [List.length_cons] at hlen1
        have hWalk := sv_walkLit_some_evals allSat clauseSat w sx s1 sm (List.replicate k false) v pol hp
        have hIH := sv_nextLit_none_evals allSat w sm k (clauseSat || ((walkWitness v w []).1.head?.getD false == pol)) s1 h
        exact evalsMono (evalsTrans (evalsTrans hStep hWalk) hIH) (by omega)

-- Step and evaluation lemmas for readLitCount

theorem sv_step_rlc_false (allSat : Bool) (w r sm sk : List Bool) :
    satVerifierTM.step (svCfg (some (.readLitCount allSat)) w [] (false :: r) sm sk) =
      some (svCfg (some (.readLitCount allSat)) w [] r sm (false :: sk)) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

theorem sv_step_rlc_true (allSat : Bool) (w r sm sk : List Bool) :
    satVerifierTM.step (svCfg (some (.readLitCount allSat)) w [] (true :: r) sm sk) =
      some (svCfg (some (.nextLit allSat false)) w [] r sm sk) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

theorem sv_step_rlc_nil (allSat : Bool) (w sm sk : List Bool) :
    satVerifierTM.step (svCfg (some (.readLitCount allSat)) w [] [] sm sk) =
      some (svCfg (some (.finish false)) w [] [] sm sk) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

def sv_rlc_rep (allSat : Bool) : ∀ (k : Nat) (w r sm sk : List Bool),
    Turing.EvalsToInTime satVerifierTM.step
      (svCfg (some (.readLitCount allSat)) w [] (List.replicate k false ++ r) sm sk)
      (some (svCfg (some (.readLitCount allSat)) w [] r sm (List.replicate k false ++ sk)))
      k
  | 0, w, r, sm, sk => by
    simpa using evalsRefl (svCfg (some (.readLitCount allSat)) w [] r sm sk)
  | k + 1, w, r, sm, sk => by
    simp only [List.replicate_succ, List.cons_append]
    have h1 := evalsInOne (sv_step_rlc_false allSat w (List.replicate k false ++ r) sm sk)
    have h2 := sv_rlc_rep allSat k w r sm (false :: sk)
    rw [replicate_false_append_cons k sk] at h2
    exact evalsMono (evalsTrans h1 h2) (by omega)

def sv_rlc_some_evals (allSat : Bool) (w sx s1 s2 sm : List Bool) (k : Nat) (cSat : Bool)
    (hp : parseUnary sx = some (k, s1))
    (hl : streamLits w false k s1 = some (cSat, s2)) :
    Turing.EvalsToInTime satVerifierTM.step
      (svCfg (some (.readLitCount allSat)) w [] sx sm [])
      (some (svCfg (some (.nextClause (allSat && cSat))) w [] s2 sm []))
      (3 * (sx.length - s2.length)) := by
  have hsx : sx = List.replicate k false ++ (true :: s1) := by
    simpa [unaryNat, List.append_assoc] using (parseUnary_exact sx s1 k).mp hp
  have hlen1 := parseUnary_rest_length_eq hp
  have hlen2 := streamLits_rest_le w k false s1 s2 cSat hl
  have h1 := sv_rlc_rep allSat k w (true :: s1) sm []
  rw [List.append_nil, ← hsx] at h1
  have h2 := evalsInOne (sv_step_rlc_true allSat w s1 sm (List.replicate k false))
  have h3 := sv_nextLit_some_evals allSat w sm k false s1 s2 cSat hl
  exact evalsMono (evalsTrans (evalsTrans h1 h2) h3) (by omega)

def sv_rlc_none_parse_evals (allSat : Bool) (w sx sm : List Bool)
    (hp : parseUnary sx = none) :
    Turing.EvalsToInTime satVerifierTM.step
      (svCfg (some (.readLitCount allSat)) w [] sx sm [])
      (some (Turing.haltList satVerifierTM [false]))
      (3 * sx.length + w.length + sm.length + 3) := by
  have hsx : sx = List.replicate sx.length false :=
    eq_replicate_false_of_parseUnary_none sx hp
  have h1 := sv_rlc_rep allSat sx.length w [] sm []
  rw [List.append_nil, ← hsx] at h1
  have h2 := evalsInOne (sv_step_rlc_nil allSat w sm sx)
  have h3 := sv_finish_evals false w [] [] sm sx
  simp only [List.length_nil] at h3
  exact evalsMono (evalsTrans (evalsTrans h1 h2) h3) (by omega)

def sv_rlc_none_lits_evals (allSat : Bool) (w sx s1 sm : List Bool) (k : Nat)
    (hp : parseUnary sx = some (k, s1))
    (hl : streamLits w false k s1 = none) :
    Turing.EvalsToInTime satVerifierTM.step
      (svCfg (some (.readLitCount allSat)) w [] sx sm [])
      (some (Turing.haltList satVerifierTM [false]))
      (3 * sx.length + w.length + sm.length + 3) := by
  have hsx : sx = List.replicate k false ++ (true :: s1) := by
    simpa [unaryNat, List.append_assoc] using (parseUnary_exact sx s1 k).mp hp
  have hlen1 := parseUnary_rest_length_eq hp
  have h1 := sv_rlc_rep allSat k w (true :: s1) sm []
  rw [List.append_nil, ← hsx] at h1
  have h2 := evalsInOne (sv_step_rlc_true allSat w s1 sm (List.replicate k false))
  have h3 := sv_nextLit_none_evals allSat w sm k false s1 hl
  exact evalsMono (evalsTrans (evalsTrans h1 h2) h3) (by omega)

-- Step and evaluation lemmas for nextClause and readClauseCount

def clauseLoopResult (w : BitString) (allSat : Bool) (m : Nat) (sx : BitString) : Bool :=
  match streamClauses w allSat m sx with
  | some (res, []) => res
  | _ => false

theorem sv_step_nextClause_nil_nil (allSat : Bool) (w : List Bool) :
    satVerifierTM.step (svCfg (some (.nextClause allSat)) w [] [] [] []) =
      some (svCfg (some (.finish allSat)) w [] [] [] []) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

theorem sv_step_nextClause_nil_cons (allSat b : Bool) (w rest : List Bool) :
    satVerifierTM.step (svCfg (some (.nextClause allSat)) w [] (b :: rest) [] []) =
      some (svCfg (some (.finish false)) w [] rest [] []) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

theorem sv_step_nextClause_cons (allSat b : Bool) (w sx sm : List Bool) :
    satVerifierTM.step (svCfg (some (.nextClause allSat)) w [] sx (b :: sm) []) =
      some (svCfg (some (.readLitCount allSat)) w [] sx sm []) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

def sv_nextClause_evals (w : List Bool) :
    ∀ (m : Nat) (allSat : Bool) (sx : List Bool),
      Turing.EvalsToInTime satVerifierTM.step
        (svCfg (some (.nextClause allSat)) w [] sx (List.replicate m false) [])
        (some (Turing.haltList satVerifierTM [clauseLoopResult w allSat m sx]))
        (3 * sx.length + w.length + m + 4)
  | 0, allSat, [] => by
    dsimp [clauseLoopResult, streamClauses]
    have h1 := evalsInOne (sv_step_nextClause_nil_nil allSat w)
    have h2 := sv_finish_evals allSat w [] [] [] []
    simp only [List.length_nil] at h2
    exact evalsMono (evalsTrans h1 h2) (by omega)
  | 0, allSat, b :: rest => by
    dsimp [clauseLoopResult, streamClauses]
    have h1 := evalsInOne (sv_step_nextClause_nil_cons allSat b w rest)
    have h2 := sv_finish_evals false w [] rest [] []
    simp only [List.length_nil] at h2
    exact evalsMono (evalsTrans h1 h2) (by simp; omega)
  | m + 1, allSat, sx => by
    have hStep := evalsInOne (sv_step_nextClause_cons allSat false w sx (List.replicate m false))
    unfold clauseLoopResult streamClauses
    cases hp : parseUnary sx with
    | none =>
      dsimp only
      have hRlc := sv_rlc_none_parse_evals allSat w sx (List.replicate m false) hp
      simp only [List.length_replicate] at hRlc
      exact evalsMono (evalsTrans hStep hRlc) (by omega)
    | some pr =>
      rcases pr with ⟨k, s1⟩
      dsimp only
      cases hl : streamLits w false k s1 with
      | none =>
        dsimp only
        have hRlc := sv_rlc_none_lits_evals allSat w sx s1 (List.replicate m false) k hp hl
        simp only [List.length_replicate] at hRlc
        exact evalsMono (evalsTrans hStep hRlc) (by omega)
      | some pr2 =>
        rcases pr2 with ⟨cSat, s2⟩
        dsimp only
        have hlen1 := parseUnary_rest_length_eq hp
        have hlen2 := streamLits_rest_le w k false s1 s2 cSat hl
        have hRlc := sv_rlc_some_evals allSat w sx s1 s2 (List.replicate m false) k cSat hp hl
        have hIH := sv_nextClause_evals w m (allSat && cSat) s2
        unfold clauseLoopResult at hIH
        exact evalsMono (evalsTrans (evalsTrans hStep hRlc) hIH) (by omega)

-- Step and evaluation lemmas for readClauseCount

theorem sv_step_rcc_false (w r sm : List Bool) :
    satVerifierTM.step (svCfg (some .readClauseCount) w [] (false :: r) sm []) =
      some (svCfg (some .readClauseCount) w [] r (false :: sm) []) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

theorem sv_step_rcc_true (w r sm : List Bool) :
    satVerifierTM.step (svCfg (some .readClauseCount) w [] (true :: r) sm []) =
      some (svCfg (some (.nextClause true)) w [] r sm []) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

theorem sv_step_rcc_nil (w sm : List Bool) :
    satVerifierTM.step (svCfg (some .readClauseCount) w [] [] sm []) =
      some (svCfg (some (.finish false)) w [] [] sm []) :=
  congrArg some (svCfg_ext (fun k => by cases k <;> rfl))

def sv_rcc_rep : ∀ (m : Nat) (w r sm : List Bool),
    Turing.EvalsToInTime satVerifierTM.step
      (svCfg (some .readClauseCount) w [] (List.replicate m false ++ r) sm [])
      (some (svCfg (some .readClauseCount) w [] r (List.replicate m false ++ sm) []))
      m
  | 0, w, r, sm => by
    simpa using evalsRefl (svCfg (some .readClauseCount) w [] r sm [])
  | m + 1, w, r, sm => by
    simp only [List.replicate_succ, List.cons_append]
    have h1 := evalsInOne (sv_step_rcc_false w (List.replicate m false ++ r) sm)
    have h2 := sv_rcc_rep m w r (false :: sm)
    rw [replicate_false_append_cons m sm] at h2
    exact evalsMono (evalsTrans h1 h2) (by omega)

def sv_rcc_evals (w x : List Bool) :
    Turing.EvalsToInTime satVerifierTM.step
      (svCfg (some .readClauseCount) w [] x [] [])
      (some (Turing.haltList satVerifierTM [
        match parseUnary x with
        | some (m, s1) => clauseLoopResult w true m s1
        | none => false
      ]))
      (3 * x.length + w.length + 5) := by
  cases hp : parseUnary x with
  | none =>
    have hx : x = List.replicate x.length false :=
      eq_replicate_false_of_parseUnary_none x hp
    have h1 := sv_rcc_rep x.length w [] []
    rw [List.append_nil, ← hx] at h1
    have h2 := evalsInOne (sv_step_rcc_nil w x)
    have h3 := sv_finish_evals false w [] [] x []
    simp only [List.length_nil] at h3
    exact evalsMono (evalsTrans (evalsTrans h1 h2) h3) (by omega)
  | some pr =>
    rcases pr with ⟨m, s1⟩
    have hx : x = List.replicate m false ++ (true :: s1) := by
      simpa [unaryNat, List.append_assoc] using (parseUnary_exact x s1 m).mp hp
    have hlen := parseUnary_rest_length_eq hp
    have h1 := sv_rcc_rep m w (true :: s1) []
    rw [List.append_nil, ← hx] at h1
    have h2 := evalsInOne (sv_step_rcc_true w s1 (List.replicate m false))
    have h3 := sv_nextClause_evals w m true s1
    exact evalsMono (evalsTrans (evalsTrans h1 h2) h3) (by omega)

def satVerifierTM_evals (u : List Bool) :
    Turing.EvalsToInTime satVerifierTM.step
      (Turing.initList satVerifierTM u)
      (some (Turing.haltList satVerifierTM [satVerifierBool u]))
      (6 * u.length + 7) := by
  rw [svCfg_init, ← satVerifierStream_eq]
  unfold satVerifierStream
  dsimp only
  have hScan := sv_splitScan_evals u []
  simp only [List.append_nil] at hScan
  have hRev := sv_splitRev_evals (pairDecodeFirst u).reverse (pairDecodeSecond u) []
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hRev
  have hRcc := sv_rcc_evals (pairDecodeSecond u) (pairDecodeFirst u)
  unfold clauseLoopResult at hRcc
  have hlen1 := pairDecodeFirst_length_le u
  have hlen2 := pairDecodeSecond_length_le u
  exact evalsMono (evalsTrans (evalsTrans hScan hRev) hRcc) (by omega)

noncomputable def satVerifierTMComputableInPolyTime :
    Turing.TM2ComputableInPolyTime finEncodingBitString finEncodingBoolBool satVerifierBool where
  tm := satVerifierTM
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 6 * Polynomial.X + Polynomial.C 7
  outputsFun u := by
    have h := satVerifierTM_evals u
    have h' : Turing.EvalsToInTime satVerifierTM.step
        (Turing.initList satVerifierTM u)
        (some (Turing.haltList satVerifierTM [satVerifierBool u]))
        ((Polynomial.C 6 * Polynomial.X + Polynomial.C 7).eval u.length) := by
      refine evalsMono h ?_
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
      omega
    change Turing.EvalsToInTime satVerifierTM.step
      (Turing.initList satVerifierTM (List.map id u))
      (some (Turing.haltList satVerifierTM [satVerifierBool u]))
      ((Polynomial.C 6 * Polynomial.X + Polynomial.C 7).eval u.length)
    rw [List.map_id]
    exact h'

theorem satVerifierBool_polyComputable :
    Nonempty (Turing.TM2ComputableInPolyTime finEncodingBitString finEncodingBoolBool satVerifierBool) :=
  ⟨satVerifierTMComputableInPolyTime⟩

theorem satVerifierLang_in_P : InP satVerifierLang :=
  edge_bool_verifier_to_verifier_in_p satVerifierBool_iff satVerifierBool_polyComputable

theorem cnf_sat_in_np_uncond : InNP CNF_SAT :=
  sat_in_np_from_verifier_in_p satVerifierLang_in_P

/-- If the encoded SAT language is outside P, it witnesses separation. -/
theorem cnf_sat_not_in_P_implies_pneqnp (h : ¬ InP CNF_SAT) : PNeqNP :=
  ⟨CNF_SAT, cnf_sat_in_np_uncond, h⟩

end ComplexitySAT
