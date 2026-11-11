import Mathlib.Computability.TMComputable

/-! Binary languages with deterministic polynomial-time deciders and polynomially bounded certificates. -/

set_option autoImplicit false

namespace ComplexitySAT

open Turing Computability

/-- Binary strings: the universal input type. -/
abbrev BitString := List Bool

/-- A decision problem (language) over binary strings. -/
abbrev Language := BitString → Prop

/-- Identity encoding of bit strings over the alphabet `Bool`
(so input length = string length). -/
def finEncodingBitString : FinEncoding BitString where
  Γ := Bool
  encode := id
  decode := Option.some
  decode_encode := fun _ => rfl
  ΓFin := inferInstance

/-- `L ∈ P`: some total Boolean function `f` agrees with `L` everywhere and is
computed by a `FinTM2` within a polynomial number of steps in the input length. -/
def InP (L : Language) : Prop :=
  ∃ f : BitString → Bool,
    Nonempty (TM2ComputableInPolyTime finEncodingBitString finEncodingBoolBool f) ∧
    ∀ x, L x ↔ f x = true

/-- Self-delimiting pairing of an instance `x` with a witness `w`:
every bit of `x` is prefixed by `false`, then a single `true` marker, then `w`.
Decodable left-to-right in linear time. -/
def pairEncode (x w : BitString) : BitString :=
  (x.flatMap fun b => [false, b]) ++ true :: w

/-- `L ∈ NP` (verifier definition): there is a polynomial-time verifier `V` and a
polynomial `p` such that `x ∈ L` iff some witness of length `≤ p(|x|)` makes `V`
accept the pair `⟨x, w⟩`. -/
def InNP (L : Language) : Prop :=
  ∃ (V : Language) (p : Polynomial ℕ), InP V ∧
    ∀ x, L x ↔ ∃ w : BitString, w.length ≤ p.eval x.length ∧ V (pairEncode x w)

/-- The class P. -/
def PClass : Set Language := {L | InP L}

/-- The class NP. -/
def NPClass : Set Language := {L | InNP L}

/-- Target statement (separation). -/
def PNeqNP : Prop := ∃ L : Language, InNP L ∧ ¬ InP L

/-- Target statement (collapse). -/
def PEqNP : Prop := ∀ L : Language, InNP L → InP L

@[simp] theorem pairEncode_nil (w : BitString) : pairEncode [] w = true :: w := by
  simp [pairEncode]

@[simp] theorem pairEncode_cons (b : Bool) (xs w : BitString) :
    pairEncode (b :: xs) w = false :: b :: pairEncode xs w := by
  simp [pairEncode]

/-- F1: the pairing is injective in both components. -/
theorem pairEncode_injective {x x' w w' : BitString}
    (h : pairEncode x w = pairEncode x' w') : x = x' ∧ w = w' := by
  induction x generalizing x' with
  | nil =>
    cases x' with
    | nil => simpa using h
    | cons b xs => simp at h
  | cons b xs ih =>
    cases x' with
    | nil => simp at h
    | cons b' xs' =>
      simp only [pairEncode_cons, List.cons.injEq, true_and] at h
      obtain ⟨hb, hrest⟩ := h
      obtain ⟨hx, hw⟩ := ih hrest
      exact ⟨by rw [hb, hx], hw⟩

/-- F2: the separation target is exactly the negation of the collapse target. -/
theorem pneqnp_iff_not_peqnp : PNeqNP ↔ ¬ PEqNP := by
  unfold PNeqNP PEqNP
  push_neg
  exact Iff.rfl

end ComplexitySAT
