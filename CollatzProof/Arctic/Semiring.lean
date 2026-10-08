/-
The arctic semiring 𝔸 = ℕ ∪ {−∞} (Definition 2.1 of the paper; Koprowski–Waldmann 2009). Addition is max, multiplication is +, zero is −∞, one is 0.
Mathlib's `MaxTropical` has no semiring structure (only `MinTropical` is a `CommSemiring`), so we give a type synonym of `WithBot ℕ`
our own `CommSemiring` instance and borrow associativity of `Matrix` multiplication and the like from Mathlib.
-/
import Mathlib

namespace Collatz.Arctic

/-- The arctic semiring ℕ ∪ {−∞}. The carrier is `WithBot ℕ` (`⊥` is −∞). -/
def Arc : Type := WithBot ℕ

namespace Arc

/-- The map to the carrier (unfolding the definition). -/
def val (a : Arc) : WithBot ℕ := a

/-- A natural number `n` read as a finite arctic value. -/
def fin (n : ℕ) : Arc := ((n : ℕ) : WithBot ℕ)

/-- −∞. -/
def negInf : Arc := (⊥ : WithBot ℕ)

instance : LinearOrder Arc := inferInstanceAs (LinearOrder (WithBot ℕ))
instance : OrderBot Arc := inferInstanceAs (OrderBot (WithBot ℕ))
instance : DecidableEq Arc := inferInstanceAs (DecidableEq (WithBot ℕ))

instance : Zero Arc := ⟨negInf⟩
instance : One Arc := ⟨fin 0⟩
instance : Add Arc := ⟨fun a b => (max (val a) (val b) : WithBot ℕ)⟩
instance : Mul Arc := ⟨fun a b => (val a + val b : WithBot ℕ)⟩

@[simp] lemma val_zero : val (0 : Arc) = ⊥ := rfl
@[simp] lemma val_one : val (1 : Arc) = ((0 : ℕ) : WithBot ℕ) := rfl
@[simp] lemma val_add (a b : Arc) : val (a + b) = max (val a) (val b) := rfl
@[simp] lemma val_mul (a b : Arc) : val (a * b) = val a + val b := rfl
@[simp] lemma val_fin (n : ℕ) : val (fin n) = ((n : ℕ) : WithBot ℕ) := rfl

lemma val_injective : Function.Injective val := fun _ _ h => h

@[ext] lemma ext {a b : Arc} (h : val a = val b) : a = b := h

lemma le_iff_val (a b : Arc) : a ≤ b ↔ val a ≤ val b := Iff.rfl

instance : CommSemiring Arc where
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

/-- **Caution (natCast)**: the image of the natural numbers in the semiring is `0 ↦ −∞`, `k + 1 ↦ 1 = fin 0` (`1 + 1 = max 0 0 = 0`).
`(k : Arc)` and `Φ + 1` do not mean the integer `k` or an increase by 1. Finite values are always written `fin k`. -/
lemma natCast_succ (k : ℕ) : ((k + 1 : ℕ) : Arc) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, ih]
    exact ext (by simp)

end Arc

end Collatz.Arctic
