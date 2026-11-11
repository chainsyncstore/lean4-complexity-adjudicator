import ComplexitySAT.Classes

/-! CNF syntax, unary length-prefixed encoding, Boolean evaluation, and a finite exhaustive SAT decider. -/

set_option autoImplicit false

namespace ComplexitySAT

open Turing Computability Polynomial

abbrev Literal := Nat × Bool
abbrev Clause := List Literal
abbrev CNF := List Clause

def unaryNat (n : Nat) : ComplexitySAT.BitString := List.replicate n false ++ [true]
def literalCode (l : Literal) : ComplexitySAT.BitString := unaryNat l.1 ++ [l.2]
def clauseCode (c : Clause) : ComplexitySAT.BitString := unaryNat c.length ++ c.flatMap literalCode
def cnfCode (f : CNF) : ComplexitySAT.BitString := unaryNat f.length ++ f.flatMap clauseCode

def cnfSatisfies (a : ComplexitySAT.BitString) (f : CNF) : Prop :=
  ∀ c, c ∈ f → ∃ l, l ∈ c ∧ a.getD l.1 false = l.2

def CNF_SAT : ComplexitySAT.Language := fun x =>
  ∃ f : CNF, ∃ a : ComplexitySAT.BitString, cnfCode f = x ∧ cnfSatisfies a f

def pairDecodeFirst : BitString → BitString
  | false :: b :: rest => b :: pairDecodeFirst rest
  | _ => []

theorem pairDecodeFirst_pairEncode (x w : BitString) :
    pairDecodeFirst (pairEncode x w) = x := by
  induction x with
  | nil =>
      simp [pairDecodeFirst, pairEncode_nil]
  | cons b xs ih =>
      rw [pairEncode_cons]
      simp [pairDecodeFirst, ih]

def pairDecodeSecond : BitString → BitString
  | [] => []
  | true :: w => w
  | false :: [] => []
  | false :: _ :: rest => pairDecodeSecond rest

theorem pairDecodeSecond_pairEncode (x w : BitString) :
    pairDecodeSecond (pairEncode x w) = w := by
  induction x with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem pairDecodeFirst_length_le : ∀ (s : BitString), (pairDecodeFirst s).length ≤ s.length
  | [] => by simp [pairDecodeFirst]
  | [false] => by simp [pairDecodeFirst]
  | false :: b :: rest => by
    dsimp [pairDecodeFirst]
    have ih := pairDecodeFirst_length_le rest
    omega
  | true :: rest => by simp [pairDecodeFirst]

theorem pairDecodeSecond_length_le : ∀ (s : BitString), (pairDecodeSecond s).length ≤ s.length
  | [] => by simp [pairDecodeSecond]
  | true :: w => by simp [pairDecodeSecond]
  | [false] => by simp [pairDecodeSecond]
  | false :: _ :: rest => by
    dsimp [pairDecodeSecond]
    have ih := pairDecodeSecond_length_le rest
    omega

def evalLiteral (a : BitString) (l : Literal) : Bool :=
  decide (a.getD l.1 false = l.2)

def evalClause (a : BitString) (c : Clause) : Bool :=
  c.any (evalLiteral a)

def evalCNF (a : BitString) (f : CNF) : Bool :=
  f.all (evalClause a)

theorem evalCNF_iff_cnfSatisfies (a : BitString) (f : CNF) :
    evalCNF a f = true ↔ cnfSatisfies a f := by
  simp [evalCNF, evalClause, evalLiteral, cnfSatisfies]

theorem length_le_flatMap_of_mem {α : Type} (g : α → BitString) (a : α) (xs : List α)
    (h : a ∈ xs) : (g a).length ≤ (xs.flatMap g).length := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    simp only [List.flatMap_cons, List.length_append]
    rcases h with rfl | hmem
    · omega
    · have := ih hmem
      omega

theorem cnf_var_lt_code_len (f : CNF) (c : Clause) (l : Literal)
    (hc : c ∈ f) (hl : l ∈ c) : l.1 < (cnfCode f).length := by
  have h1 : (literalCode l).length = l.1 + 2 := by
    simp [literalCode, unaryNat]
  have h2 : (literalCode l).length ≤ (c.flatMap literalCode).length :=
    length_le_flatMap_of_mem literalCode l c hl
  have h3 : (c.flatMap literalCode).length ≤ (clauseCode c).length := by
    simp [clauseCode, unaryNat]
    omega
  have h4 : (clauseCode c).length ≤ (f.flatMap clauseCode).length :=
    length_le_flatMap_of_mem clauseCode c f hc
  have h5 : (cnfCode f).length = f.length + 1 + (f.flatMap clauseCode).length := by
    simp [cnfCode, unaryNat]
    omega
  omega

theorem getD_take_eq (a : BitString) (n i : Nat) (d : Bool) (hi : i < n) :
    (a.take n).getD i d = a.getD i d := by
  induction a generalizing n i with
  | nil => simp
  | cons b bs ih =>
    cases n with
    | zero => omega
    | succ n' =>
      cases i with
      | zero => rfl
      | succ i' =>
        have hi' : i' < n' := by omega
        simpa [List.take] using ih n' i' hi'

theorem cnfSatisfies_take (a : BitString) (f : CNF) :
    cnfSatisfies (a.take (cnfCode f).length) f ↔ cnfSatisfies a f := by
  constructor
  · intro h c hc
    rcases h c hc with ⟨l, hl, heval⟩
    refine ⟨l, hl, ?_⟩
    have hlt := cnf_var_lt_code_len f c l hc hl
    rwa [getD_take_eq a (cnfCode f).length l.1 false hlt] at heval
  · intro h c hc
    rcases h c hc with ⟨l, hl, heval⟩
    refine ⟨l, hl, ?_⟩
    have hlt := cnf_var_lt_code_len f c l hc hl
    rwa [getD_take_eq a (cnfCode f).length l.1 false hlt]

def satVerifierLang : Language := fun u =>
  ∃ f : CNF, cnfCode f = pairDecodeFirst u ∧ evalCNF (pairDecodeSecond u) f = true

theorem sat_linear_witness_bound (x : BitString) :
    CNF_SAT x ↔
      ∃ w : BitString, w.length ≤ (Polynomial.X : Polynomial ℕ).eval x.length ∧
        satVerifierLang (pairEncode x w) := by
  constructor
  · rintro ⟨f, a, hcode, hsat⟩
    refine ⟨a.take x.length, ?_, ?_⟩
    · simp only [Polynomial.eval_X]
      exact List.length_take_le x.length a
    · refine ⟨f, ?_, ?_⟩
      · rw [pairDecodeFirst_pairEncode]
        exact hcode
      · rw [pairDecodeSecond_pairEncode, evalCNF_iff_cnfSatisfies, ← hcode]
        exact (cnfSatisfies_take a f).mpr hsat
  · rintro ⟨w, _, f, hcode, heval⟩
    rw [pairDecodeFirst_pairEncode] at hcode
    rw [pairDecodeSecond_pairEncode, evalCNF_iff_cnfSatisfies] at heval
    exact ⟨f, w, hcode, heval⟩

theorem edge_verifier_to_sat_in_np
    (hBound : ∀ x : BitString,
      CNF_SAT x ↔
        ∃ w : BitString, w.length ≤ (Polynomial.X : Polynomial ℕ).eval x.length ∧
          satVerifierLang (pairEncode x w))
    (hVerP : InP satVerifierLang) :
    InNP CNF_SAT :=
  ⟨satVerifierLang, Polynomial.X, hVerP, hBound⟩

theorem sat_in_np_from_verifier_in_p (hVerP : InP satVerifierLang) :
    InNP CNF_SAT :=
  edge_verifier_to_sat_in_np sat_linear_witness_bound hVerP

theorem unaryNat_zero : unaryNat 0 = [true] := rfl

theorem unaryNat_succ (n : Nat) : unaryNat (n + 1) = false :: unaryNat n := rfl

def parseUnary : BitString → Option (Nat × BitString)
  | [] => none
  | true :: rest => some (0, rest)
  | false :: rest =>
    match parseUnary rest with
    | some (n, r) => some (n + 1, r)
    | none => none

theorem parseUnary_exact (s rest : BitString) (n : Nat) :
    parseUnary s = some (n, rest) ↔ s = unaryNat n ++ rest := by
  induction s generalizing n with
  | nil =>
    constructor
    · intro h
      cases h
    · intro h
      cases n <;> simp [unaryNat_zero, unaryNat_succ] at h
  | cons b bs ih =>
    cases b with
    | true =>
      constructor
      · intro h
        simp only [parseUnary, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rfl
      · intro h
        cases n with
        | zero =>
          simp only [unaryNat_zero, List.cons_append, List.nil_append, List.cons.injEq,
            true_and] at h
          subst h
          rfl
        | succ n' =>
          simp [unaryNat_succ] at h
    | false =>
      constructor
      · intro h
        simp only [parseUnary] at h
        cases hp : parseUnary bs with
        | none =>
          rw [hp] at h
          cases h
        | some pr =>
          rcases pr with ⟨m, r⟩
          rw [hp] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          have hbs : bs = unaryNat m ++ r := (ih m).mp hp
          rw [hbs, unaryNat_succ, List.cons_append]
      · intro h
        cases n with
        | zero =>
          simp [unaryNat_zero] at h
        | succ n' =>
          simp only [unaryNat_succ, List.cons_append, List.cons.injEq, true_and] at h
          have hp : parseUnary bs = some (n', rest) := (ih n').mpr h
          simp [parseUnary, hp]

def parseLiteral (s : BitString) : Option (Literal × BitString) :=
  match parseUnary s with
  | some (v, b :: rest) => some ((v, b), rest)
  | _ => none

theorem parseLiteral_exact (s rest : BitString) (l : Literal) :
    parseLiteral s = some (l, rest) ↔ s = literalCode l ++ rest := by
  rcases l with ⟨v, b⟩
  constructor
  · intro h
    unfold parseLiteral at h
    cases hp : parseUnary s with
    | none =>
      rw [hp] at h
      cases h
    | some pr =>
      rcases pr with ⟨v', r⟩
      rw [hp] at h
      cases r with
      | nil =>
        cases h
      | cons b' r' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
        have hs : s = unaryNat v' ++ (b' :: r') := (parseUnary_exact s (b' :: r') v').mp hp
        simpa [literalCode, List.append_assoc] using hs
  · intro h
    have hs : s = unaryNat v ++ (b :: rest) := by
      simpa [literalCode, List.append_assoc] using h
    have hp : parseUnary s = some (v, b :: rest) := (parseUnary_exact s (b :: rest) v).mpr hs
    simp [parseLiteral, hp]

def parseMany {α : Type} (p : BitString → Option (α × BitString)) :
    Nat → BitString → Option (List α × BitString)
  | 0, s => some ([], s)
  | k + 1, s =>
    match p s with
    | some (a, s1) =>
      match parseMany p k s1 with
      | some (as, s2) => some (a :: as, s2)
      | none => none
    | none => none

theorem parseMany_exact {α : Type} (p : BitString → Option (α × BitString)) (enc : α → BitString)
    (hp : ∀ (s rest : BitString) (a : α), p s = some (a, rest) ↔ s = enc a ++ rest) :
    ∀ (k : Nat) (s rest : BitString) (as : List α),
      parseMany p k s = some (as, rest) ↔ as.length = k ∧ s = as.flatMap enc ++ rest := by
  intro k
  induction k with
  | zero =>
    intro s rest as
    constructor
    · intro h
      simp only [parseMany, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    · rintro ⟨hlen, rfl⟩
      cases as with
      | nil => rfl
      | cons _ _ => simp at hlen
  | succ k ih =>
    intro s rest as
    constructor
    · intro h
      unfold parseMany at h
      cases hp1 : p s with
      | none =>
        rw [hp1] at h
        cases h
      | some pr1 =>
        rcases pr1 with ⟨a, s1⟩
        rw [hp1] at h
        dsimp only at h
        cases hp2 : parseMany p k s1 with
        | none =>
          rw [hp2] at h
          cases h
        | some pr2 =>
          rcases pr2 with ⟨as', s2⟩
          rw [hp2] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          have hs1 : s = enc a ++ s1 := (hp s s1 a).mp hp1
          rcases (ih s1 s2 as').mp hp2 with ⟨hlen, hs2⟩
          refine ⟨by simp [hlen], ?_⟩
          rw [hs1, hs2, List.flatMap_cons, List.append_assoc]
    · rintro ⟨hlen, hs⟩
      cases as with
      | nil => simp at hlen
      | cons a as' =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        rw [List.flatMap_cons, List.append_assoc] at hs
        have hp1 : p s = some (a, as'.flatMap enc ++ rest) :=
          (hp s (as'.flatMap enc ++ rest) a).mpr hs
        have hp2 : parseMany p k (as'.flatMap enc ++ rest) = some (as', rest) :=
          (ih (as'.flatMap enc ++ rest) rest as').mpr ⟨hlen, rfl⟩
        simp [parseMany, hp1, hp2]

def parseClause (s : BitString) : Option (Clause × BitString) :=
  match parseUnary s with
  | some (k, s1) => parseMany parseLiteral k s1
  | none => none

theorem parseClause_exact (s rest : BitString) (c : Clause) :
    parseClause s = some (c, rest) ↔ s = clauseCode c ++ rest := by
  constructor
  · intro h
    unfold parseClause at h
    cases hp : parseUnary s with
    | none =>
      rw [hp] at h
      cases h
    | some pr =>
      rcases pr with ⟨k, s1⟩
      rw [hp] at h
      have hs : s = unaryNat k ++ s1 := (parseUnary_exact s s1 k).mp hp
      rcases (parseMany_exact parseLiteral literalCode parseLiteral_exact k s1 rest c).mp h with ⟨hlen, hs1⟩
      subst hlen
      simpa [clauseCode, List.append_assoc] using hs.trans (congrArg (unaryNat c.length ++ ·) hs1)
  · intro h
    have hs : s = unaryNat c.length ++ (c.flatMap literalCode ++ rest) := by
      simpa [clauseCode, List.append_assoc] using h
    have hp : parseUnary s = some (c.length, c.flatMap literalCode ++ rest) :=
      (parseUnary_exact s (c.flatMap literalCode ++ rest) c.length).mpr hs
    have hm : parseMany parseLiteral c.length (c.flatMap literalCode ++ rest) = some (c, rest) :=
      (parseMany_exact parseLiteral literalCode parseLiteral_exact c.length
        (c.flatMap literalCode ++ rest) rest c).mpr ⟨rfl, rfl⟩
    simp [parseClause, hp, hm]

def cnfDecode (s : BitString) : Option CNF :=
  match parseUnary s with
  | some (m, s1) =>
    match parseMany parseClause m s1 with
    | some (f, []) => some f
    | _ => none
  | none => none

theorem cnfDecode_iff_code (s : BitString) (f : CNF) :
    cnfDecode s = some f ↔ cnfCode f = s := by
  constructor
  · intro h
    unfold cnfDecode at h
    cases hp : parseUnary s with
    | none =>
      rw [hp] at h
      cases h
    | some pr =>
      rcases pr with ⟨m, s1⟩
      rw [hp] at h
      dsimp only at h
      cases hm : parseMany parseClause m s1 with
      | none =>
        rw [hm] at h
        cases h
      | some pr2 =>
        rcases pr2 with ⟨f', r⟩
        rw [hm] at h
        cases r with
        | nil =>
          simp only [Option.some.injEq] at h
          subst h
          have hs : s = unaryNat m ++ s1 := (parseUnary_exact s s1 m).mp hp
          rcases (parseMany_exact parseClause clauseCode parseClause_exact m s1 [] f').mp hm with ⟨hlen, hs1⟩
          subst hlen
          rw [List.append_nil] at hs1
          rw [hs, hs1]
          rfl
        | cons _ _ =>
          cases h
  · intro h
    subst h
    have hs : cnfCode f = unaryNat f.length ++ (f.flatMap clauseCode ++ []) := by
      simp [cnfCode]
    have hp : parseUnary (cnfCode f) = some (f.length, f.flatMap clauseCode) := by
      have hp' := (parseUnary_exact (cnfCode f) (f.flatMap clauseCode) f.length).mpr (by rfl)
      exact hp'
    have hm : parseMany parseClause f.length (f.flatMap clauseCode) = some (f, []) :=
      (parseMany_exact parseClause clauseCode parseClause_exact f.length
        (f.flatMap clauseCode) [] f).mpr ⟨rfl, by simp⟩
    simp [cnfDecode, hp, hm]

theorem cnfDecode_left_inv (f : CNF) :
    cnfDecode (cnfCode f) = some f :=
  (cnfDecode_iff_code (cnfCode f) f).mpr rfl

def satVerifierBool (u : BitString) : Bool :=
  match cnfDecode (pairDecodeFirst u) with
  | some f => evalCNF (pairDecodeSecond u) f
  | none => false

theorem satVerifierBool_iff (u : BitString) :
    satVerifierBool u = true ↔ satVerifierLang u := by
  unfold satVerifierBool satVerifierLang
  cases hd : cnfDecode (pairDecodeFirst u) with
  | none =>
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro f hcode _
    have hsome : cnfDecode (pairDecodeFirst u) = some f :=
      (cnfDecode_iff_code (pairDecodeFirst u) f).mpr hcode
    rw [hd] at hsome
    cases hsome
  | some f =>
    simp only
    constructor
    · intro heval
      exact ⟨f, (cnfDecode_iff_code (pairDecodeFirst u) f).mp hd, heval⟩
    · rintro ⟨f', hcode, heval⟩
      have hsome : cnfDecode (pairDecodeFirst u) = some f' :=
        (cnfDecode_iff_code (pairDecodeFirst u) f').mpr hcode
      rw [hd] at hsome
      injection hsome with hff
      subst hff
      exact heval

theorem sat_iff_bounded_verifier_bool (x : BitString) :
    CNF_SAT x ↔
      ∃ w : BitString, w.length ≤ x.length ∧ satVerifierBool (pairEncode x w) = true := by
  rw [sat_linear_witness_bound x]
  simp only [Polynomial.eval_X]
  constructor
  · rintro ⟨w, hlen, hver⟩
    exact ⟨w, hlen, (satVerifierBool_iff (pairEncode x w)).mpr hver⟩
  · rintro ⟨w, hlen, hbool⟩
    exact ⟨w, hlen, (satVerifierBool_iff (pairEncode x w)).mp hbool⟩

def bitStringsOfLen : Nat → List BitString
  | 0 => [[]]
  | n + 1 => (bitStringsOfLen n).map (false :: ·) ++ (bitStringsOfLen n).map (true :: ·)

theorem mem_bitStringsOfLen : ∀ (n : Nat) (w : BitString),
    w ∈ bitStringsOfLen n ↔ w.length = n
  | 0, w => by
    simp only [bitStringsOfLen, List.mem_singleton]
    constructor
    · rintro rfl; rfl
    · intro h; exact List.eq_nil_of_length_eq_zero h
  | n + 1, w => by
    simp only [bitStringsOfLen, List.mem_append, List.mem_map]
    constructor
    · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
      · simp [(mem_bitStringsOfLen n u).mp hu]
      · simp [(mem_bitStringsOfLen n u).mp hu]
    · intro hlen
      cases w with
      | nil => simp at hlen
      | cons b u =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        have hu : u ∈ bitStringsOfLen n := (mem_bitStringsOfLen n u).mpr hlen
        cases b
        · exact Or.inl ⟨u, hu, rfl⟩
        · exact Or.inr ⟨u, hu, rfl⟩

theorem bitStringsOfLen_length : ∀ (n : Nat),
    (bitStringsOfLen n).length = 2 ^ n
  | 0 => rfl
  | n + 1 => by
    simp only [bitStringsOfLen, List.length_append, List.length_map, bitStringsOfLen_length n]
    rw [Nat.pow_succ]
    omega

def bitStringsUpTo (n : Nat) : List BitString :=
  (List.range (n + 1)).flatMap bitStringsOfLen

theorem mem_bitStringsUpTo (n : Nat) (w : BitString) :
    w ∈ bitStringsUpTo n ↔ w.length ≤ n := by
  unfold bitStringsUpTo
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨k, hk, hw⟩
    rw [List.mem_range] at hk
    have hlen : w.length = k := (mem_bitStringsOfLen k w).mp hw
    omega
  · intro hle
    refine ⟨w.length, ?_, (mem_bitStringsOfLen w.length w).mpr rfl⟩
    rw [List.mem_range]
    omega

theorem bitStringsUpTo_exact :
    (∀ (n : Nat) (w : BitString), w ∈ bitStringsOfLen n ↔ w.length = n) ∧
    (∀ (n : Nat), (bitStringsOfLen n).length = 2 ^ n) ∧
    (∀ (n : Nat) (w : BitString), w ∈ bitStringsUpTo n ↔ w.length ≤ n) :=
  ⟨mem_bitStringsOfLen, bitStringsOfLen_length, mem_bitStringsUpTo⟩

def satDeciderBool (x : BitString) : Bool :=
  (bitStringsUpTo x.length).any (fun w => satVerifierBool (pairEncode x w))

theorem satDeciderBool_iff (x : BitString) :
    satDeciderBool x = true ↔ CNF_SAT x := by
  unfold satDeciderBool
  rw [List.any_eq_true, sat_iff_bounded_verifier_bool]
  constructor
  · rintro ⟨w, hw, hver⟩
    exact ⟨w, (mem_bitStringsUpTo x.length w).mp hw, hver⟩
  · rintro ⟨w, hle, hver⟩
    exact ⟨w, (mem_bitStringsUpTo x.length w).mpr hle, hver⟩

def encodedAssignmentWitness (x w : ComplexitySAT.BitString) : Prop :=
  ∃ f : ComplexitySAT.CNF,
    ComplexitySAT.cnfCode f = x ∧ ComplexitySAT.evalCNF w f = true

theorem encodedAssignmentWitness_iff (f : CNF) (w : BitString) :
    encodedAssignmentWitness (cnfCode f) w ↔ evalCNF w f = true := by
  constructor
  · rintro ⟨g, hcode, hEval⟩
    have hdec := (cnfDecode_iff_code (cnfCode f) g).mpr hcode
    rw [cnfDecode_left_inv] at hdec
    injection hdec with hfg
    subst g
    exact hEval
  · intro hEval
    exact ⟨f, rfl, hEval⟩

theorem satDeciderBool_of_encodedAssignmentWitness {x w : BitString}
    (h : encodedAssignmentWitness x w) : satDeciderBool x = true := by
  obtain ⟨f, hcode, hEval⟩ := h
  exact (satDeciderBool_iff x).mpr ⟨f, w, hcode, (evalCNF_iff_cnfSatisfies w f).mp hEval⟩

theorem edge_bool_verifier_to_verifier_in_p
    (hIff : ∀ u : BitString, satVerifierBool u = true ↔ satVerifierLang u)
    (hTM2 : Nonempty (TM2ComputableInPolyTime finEncodingBitString finEncodingBoolBool satVerifierBool)) :
    InP satVerifierLang :=
  ⟨satVerifierBool, hTM2, fun u => (hIff u).symm⟩

end ComplexitySAT
