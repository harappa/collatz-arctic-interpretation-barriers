/-
Lean definitions for the arctic barrier (Theorem 3.1 of the paper; Sections 2.1 and 2.3).

* The system 𝒯 (`ST` in the Lean names; TPDB's `SRS_Standard/Yolcu_21/collatz-T`, the 11 rules of Paper II). The letters are named as in the paper (`f` = b0, `t` = b1,
  `d0..d2` = t0..t2, `lft` = & (the paper's `/`), `rgt` = $ (the paper's `.`)).
* Arctic interpretations (Koprowski–Waldmann 2009; Definition 2.1 of the paper): a `d × d` arctic matrix for each letter, and the product for a string.
  Weak orientation `[ℓ] ≥ [r]` (entrywise), strict orientation `[ℓ] ≫ [r]` (in each entry `>` or both −∞).
* `Φ(w) := [w]₀₀` (the paper's `[w]_{11}`; indices start at 0).
* The canonical string `can n = lft :: bin' n ++ [rgt]` (the binary digits below the leading one, from the top).
-/
import CollatzProof.Arctic.Semiring

namespace Collatz.Arctic

/-- The letters of 𝒯 (named `Letter` to avoid a clash with Mathlib's `Sym`, the symmetric power). -/
inductive Letter
  | f | t | d0 | d1 | d2 | lft | rgt
  deriving DecidableEq, Repr

/-- Strings. -/
abbrev Word := List Letter

/-- A rule `ℓ → r`. -/
structure Rule where
  lhs : Word
  rhs : Word
  deriving DecidableEq, Repr

open Letter in
/-- The 11 rules of 𝒯 (TPDB's collatz-T, in the order of the file; compared with the file by the script of Appendix C of the paper). -/
def rulesST : List Rule :=
  [ ⟨[f, rgt], [rgt]⟩, ⟨[t, rgt], [d2, rgt]⟩,                         -- dynamic rules (even step, odd step)
    ⟨[f, d0], [d0, f]⟩, ⟨[f, d1], [d0, t]⟩, ⟨[f, d2], [d1, f]⟩,      -- carry rules (a ternary digit crosses a binary digit)
    ⟨[t, d0], [d1, t]⟩, ⟨[t, d1], [d2, f]⟩, ⟨[t, d2], [d2, t]⟩,
    ⟨[lft, d0], [lft, t]⟩, ⟨[lft, d1], [lft, f, f]⟩, ⟨[lft, d2], [lft, f, t]⟩ ]  -- left-end rules

/-- One rewrite step: `p ++ ℓ ++ q → p ++ r ++ q`. -/
def Step (ρ : Rule) (u v : Word) : Prop :=
  ∃ p q : Word, u = p ++ ρ.lhs ++ q ∧ v = p ++ ρ.rhs ++ q

/-- `d × d` arctic matrices. -/
abbrev AMat (d : ℕ) := Matrix (Fin d) (Fin d) Arc

/-- Arctic interpretations. -/
abbrev Interp (d : ℕ) := Letter → AMat d

/-- The interpretation of a string (the product). -/
def ev {d : ℕ} (I : Interp d) (w : Word) : AMat d := (w.map I).prod

/-- Weak orientation `[ℓ] ≥ [r]` (entrywise). -/
def Weak {d : ℕ} (I : Interp d) (ρ : Rule) : Prop :=
  ∀ i j, ev I ρ.rhs i j ≤ ev I ρ.lhs i j

/-- Strict orientation `[ℓ] ≫ [r]` (in each entry `>` or both −∞). -/
def Strict {d : ℕ} (I : Interp d) (ρ : Rule) : Prop :=
  ∀ i j, ev I ρ.rhs i j < ev I ρ.lhs i j ∨ (ev I ρ.lhs i j = 0 ∧ ev I ρ.rhs i j = 0)

/-- The entry with index 0 (index 1 in the paper) is finite for every letter (the condition on arctic interpretations of Koprowski–Waldmann 2009). -/
def Fin00 {d : ℕ} (hd : 0 < d) (I : Interp d) : Prop :=
  ∀ s, I s ⟨0, hd⟩ ⟨0, hd⟩ ≠ 0

/-- `Φ(w) := [w]₀₀`. -/
def Phi {d : ℕ} (hd : 0 < d) (I : Interp d) (w : Word) : Arc := ev I w ⟨0, hd⟩ ⟨0, hd⟩

/-- The binary digits (from the top, without the leading 1); for `n ≥ 1`. -/
def binTail (n : ℕ) : Word :=
  ((Nat.digits 2 n).reverse.drop 1).map (fun b => if b = 0 then Letter.f else Letter.t)

/-- The canonical string `can n = lft bin'(n) rgt`. -/
def can (n : ℕ) : Word := Letter.lft :: (binTail n ++ [Letter.rgt])

/-- The shortcut Collatz map `T`. -/
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

end Collatz.Arctic
