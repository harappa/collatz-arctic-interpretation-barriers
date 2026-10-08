/-
The arctic semiring below zero 𝔸_ℤ = ℤ ∪ {−∞} (Koprowski–Waldmann 2009, Section 8; Theorem 3.4 of the paper). Addition is max, multiplication is +, zero is −∞, one is 0.
Built in the same way as `Arc` (ℕ ∪ {−∞}) of `Semiring.lean`, with carrier `WithBot ℤ`.
-/
import CollatzProof.Arctic.Semiring

namespace Collatz.Arctic

/-- The arctic semiring below zero ℤ ∪ {−∞}. The carrier is `WithBot ℤ` (`⊥` is −∞). -/
def ArcZ : Type := WithBot ℤ

namespace ArcZ

/-- The map to the carrier (unfolding the definition). -/
def val (a : ArcZ) : WithBot ℤ := a

/-- An integer `z` read as a finite arctic value. -/
def fin (z : ℤ) : ArcZ := ((z : ℤ) : WithBot ℤ)

/-- −∞. -/
def negInf : ArcZ := (⊥ : WithBot ℤ)

instance : LinearOrder ArcZ := inferInstanceAs (LinearOrder (WithBot ℤ))
instance : OrderBot ArcZ := inferInstanceAs (OrderBot (WithBot ℤ))
instance : DecidableEq ArcZ := inferInstanceAs (DecidableEq (WithBot ℤ))

instance : Zero ArcZ := ⟨negInf⟩
instance : One ArcZ := ⟨fin 0⟩
instance : Add ArcZ := ⟨fun a b => (max (val a) (val b) : WithBot ℤ)⟩
instance : Mul ArcZ := ⟨fun a b => (val a + val b : WithBot ℤ)⟩

@[simp] lemma val_zero : val (0 : ArcZ) = ⊥ := rfl
@[simp] lemma val_one : val (1 : ArcZ) = ((0 : ℤ) : WithBot ℤ) := rfl
@[simp] lemma val_add (a b : ArcZ) : val (a + b) = max (val a) (val b) := rfl
@[simp] lemma val_mul (a b : ArcZ) : val (a * b) = val a + val b := rfl
@[simp] lemma val_fin (z : ℤ) : val (fin z) = ((z : ℤ) : WithBot ℤ) := rfl

lemma val_injective : Function.Injective val := fun _ _ h => h

@[ext] lemma ext {a b : ArcZ} (h : val a = val b) : a = b := h

lemma le_iff_val (a b : ArcZ) : a ≤ b ↔ val a ≤ val b := Iff.rfl

instance : CommSemiring ArcZ where
  add_assoc a b c := ext (by simp [max_assoc])
  zero_add a := ext (by simp)
  add_zero a := ext (by simp)
  add_comm a b := ext (by simp [max_comm])
  mul_assoc a b c := ext (by simp [add_assoc])
  one_mul a := ext (by simp)
  mul_one a := ext (by simp)
  zero_mul a := ext (by simp)
  mul_zero a := ext (by simp)
  mul_comm a b := ext (by simp [add_comm])
  left_distrib a b c := ext (by simp [max_add_add_left])
  right_distrib a b c := ext (by simp [max_add_add_right])
  nsmul := nsmulRec
  npow := npowRec

/-- Embedding `Arc` (ℕ ∪ {−∞}) into `ArcZ` (finite values: natural numbers read as integers). -/
def ofArc (a : Arc) : ArcZ := WithBot.map (fun n : ℕ => (n : ℤ)) (Arc.val a)

end ArcZ

end Collatz.Arctic
