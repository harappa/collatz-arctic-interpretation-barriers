/-
Checks of the canonical strings, sweeps and canonical derivations of $R_H$ for small `n` (requested by the internal independent review).
The Python script of Appendix C checks a Python transcription, so here **the Lean definitions themselves** (`canRH`, `sweepRulesRH`,
`canDerivRH`, `liftRH`) are checked by `decide` for small `n` (no large powers are used).
This file serves only as a check and is not in the closure of the main theorem (`RH/Final.lean`).

* Simulation of string rewriting `runSeq`: applies a list of rules in order, each once at its leftmost match (in forward canonical derivations the moving digit
  is always to the left of the remaining digits). Soundness `runSeq_chain`: if `runSeq w rs = some v`, then `Chain rs w v`.
  Hence correctness of the canonical derivations for small `n` is checked by computation, independently of `canDerivRH_chain` (`RH/Canon.lean`, a proof by induction).
* `canRH n = L bin(n) .` (the binary digits of `n` via `Nat.digits`, most significant first).
* Sweeps: `L t bin'(y) d . →* L t bin'(3y + d) .` (`1 ≤ y < 64`, `d ≤ 2`).
* Canonical derivations: `canRH n →* canRH (Hmap n)` for `n < 128` in `HDom`. Explicit examples `n = 20, 23, 31` (the same as the output of
  the Python transcription of Appendix C).
* Used rules: `L0 → L` and `Lf → L` do not occur for `n < 128`.
* Numbers of uses (the equality form, for small `n`, of the inequalities of `RH/Count.lean`): equal for `ff.` and `ttt.`; `L1 → Lt` equals `/0 → /t`;
  `L2 → Ltf` equals the sum of `/1 → /ff` and `/2 → /ft`; `aRule b d` equals the number for $\mathcal H$ plus, when `b = 1`, the number of uses
  of `/d` (`n < 128`).
-/
import CollatzProof.Arctic.RH.Count

namespace Collatz.Arctic.RH

namespace CheckRH

open Collatz.Arctic HModel HTPDB Letter

/-! ## Simulation of string rewriting and its soundness -/

/-- The rest of `w` if `l` is a prefix of `w`. -/
def stripPre : Word → Word → Option Word
  | [], w => some w
  | _ :: _, [] => none
  | a :: l, b :: w => if a = b then stripPre l w else none

/-- Apply the rule `ρ` once at its leftmost match. -/
def rewriteLeft (ρ : Rule) : Word → Option Word
  | [] => (stripPre ρ.lhs []).map (fun r => ρ.rhs ++ r)
  | a :: w =>
    match stripPre ρ.lhs (a :: w) with
    | some r => some (ρ.rhs ++ r)
    | none => (rewriteLeft ρ w).map (fun v => a :: v)

/-- Apply a list of rules in order. -/
def runSeq : Word → List Rule → Option Word
  | w, [] => some w
  | w, ρ :: rs =>
    match rewriteLeft ρ w with
    | some v => runSeq v rs
    | none => none

lemma stripPre_eq : ∀ (l w r : Word), stripPre l w = some r → w = l ++ r
  | [], w, r, h => by simp [stripPre] at h; simp [h]
  | _ :: _, [], r, h => by simp [stripPre] at h
  | a :: l, b :: w, r, h => by
    simp only [stripPre] at h
    split_ifs at h with hab
    · subst hab; simp [stripPre_eq l w r h]

lemma rewriteLeft_step (ρ : Rule) : ∀ (w v : Word), rewriteLeft ρ w = some v → Step ρ w v
  | [], v, h => by
    simp only [rewriteLeft, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    exact ⟨[], r, by simpa using stripPre_eq _ _ _ hr, by simp⟩
  | a :: w, v, h => by
    simp only [rewriteLeft] at h
    split at h
    · rename_i r hr
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨[], r, by simpa using stripPre_eq _ _ _ hr, by simp⟩
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨v', hv', rfl⟩ := h
      obtain ⟨p, q, h1, h2⟩ := rewriteLeft_step ρ w v' hv'
      exact ⟨a :: p, q, by simp [h1], by simp [h2]⟩

/-- **Soundness**: if `runSeq w rs = some v`, then `Chain rs w v`. -/
theorem runSeq_chain : ∀ (rs : List Rule) (w v : Word), runSeq w rs = some v → Chain rs w v
  | [], w, v, h => by
    simp only [runSeq, Option.some.injEq] at h
    subst h; exact Chain.nil w
  | ρ :: rs, w, v, h => by
    simp only [runSeq] at h
    split at h
    · rename_i u hu
      exact Chain.cons (rewriteLeft_step ρ w u hu) (runSeq_chain rs u v h)
    · simp at h

/-! ## Canonical strings -/

/-- `canRH n = L bin(n) .` (`1 ≤ n < 64`; for general `n` see `canRH_eq_bin`). -/
example : ∀ n < 64, 1 ≤ n →
    canRH n = Letter.lft :: ((Nat.digits 2 n).reverse.map bitL ++ [Letter.rgt]) := by decide

example : canRH 1 = [lft, t, rgt] ∧ canRH 5 = [lft, t, f, t, rgt] ∧
    canRH 17 = [lft, t, f, f, f, t, rgt] := by decide

/-! ## Sweeps -/

/-- The sweep `L t bin'(y) d . →* L t bin'(3y + d) .` (`1 ≤ y < 64`, `d ≤ 2`; the general form is `sweep_chainRH`). -/
example : ∀ y < 64, 1 ≤ y → ∀ d < 3,
    runSeq (Letter.lft :: Letter.t :: (binTail y ++ digL d :: [Letter.rgt])) (sweepRulesRH (tailBitsLSB y) d) =
      some (Letter.lft :: Letter.t :: (binTail (3 * y + d) ++ [Letter.rgt])) := by decide

/-- The rule lists of sweeps and `liftRH` (`1 ≤ y < 64`, `d ≤ 2`; the general form is `sweepRulesRH_eq`). -/
example : ∀ y < 64, 1 ≤ y → ∀ d < 3,
    sweepRulesRH (tailBitsLSB y) d = (sweepRules (tailBitsLSB y) d).flatMap liftRH := by decide

/-! ## Canonical derivations -/

/-- For `n < 128` in `HDom`, applying `canDerivRH n` at leftmost matches gives `canRH (Hmap n)`. -/
theorem canon_small : ∀ n < 128, (8 ≤ n ∧ (n % 4 = 0 ∨ n % 8 = 7)) →
    runSeq (canRH n) (canDerivRH n) = some (canRH (Hmap n)) := by decide

/-- Hence (independently of the inductive proof `canDerivRH_chain`) the canonical derivations are correct for `n < 128` in `HDom`. -/
example : ∀ n < 128, HDom n → Chain (canDerivRH n) (canRH n) (canRH (Hmap n)) :=
  fun n hn hd => runSeq_chain _ _ _ (canon_small n hn hd)

/-- Explicit examples (the same lists as the Python transcription of Appendix C). `20 = Ltftff.` becomes, by `ff.`, `t0`, `f1`, `t0`, `L1`,
`15 = Ltttt.`. -/
example : canDerivRH 20 = [ffRule, aRule 1 0, aRule 0 1, aRule 1 0, leftRuleRH 1] := by decide

/-- `23 = Ltfttt.` (`m = 2`): after `ttt.`, the left 2 crosses `tf` and uses `L2`, and the right 2 crosses `bin(8) = tfff` and uses `L1`, giving
`26 = Lttftf.`. -/
example : canDerivRH 23 = [tttRule, aRule 0 2, aRule 1 1, leftRuleRH 2, aRule 0 2, aRule 0 1, aRule 0 0,
    aRule 1 0, leftRuleRH 1] := by decide

/-- From `31 = Lttttt.` (`m = 3`) to `35 = Ltffftt.`. -/
example : canDerivRH 31 = [tttRule, aRule 1 2, aRule 1 2, leftRuleRH 2, aRule 1 2, aRule 1 2, aRule 0 2,
    aRule 1 1, leftRuleRH 2] := by decide

example : Hmap 20 = 15 ∧ Hmap 23 = 26 ∧ Hmap 31 = 35 := by decide

/-! ## Used rules and numbers of uses -/

/-- `L0 → L` and `Lf → L` do not occur in canonical derivations (`n < 128`; the general form is `canDerivRH_sub` with the definition of `usedRH`). -/
example : ∀ n < 128, l0Rule ∉ canDerivRH n ∧ lfRule ∉ canDerivRH n := by decide

/-- Equalities of numbers of uses (`n < 128`): equal for `ff.` and `ttt.`, `L1 = /0`, `L2 = /1 + /2`. -/
example : ∀ n < 128,
    (canDerivRH n).count ffRule = (canDerivH n).count ffRule ∧
    (canDerivRH n).count tttRule = (canDerivH n).count tttRule ∧
    (canDerivRH n).count (leftRuleRH 1) = (canDerivH n).count (leftRule 0) ∧
    (canDerivRH n).count (leftRuleRH 2) =
      (canDerivH n).count (leftRule 1) + (canDerivH n).count (leftRule 2) := by decide

/-- Numbers of uses of the carry rules (`n < 128`): the number for $\mathcal H$ plus, when `b = 1`, the number of uses of `/d`. -/
example : ∀ n < 128, ∀ d < 3,
    (canDerivRH n).count (aRule 0 d) = (canDerivH n).count (aRule 0 d) ∧
    (canDerivRH n).count (aRule 1 d) = (canDerivH n).count (aRule 1 d) + (canDerivH n).count (leftRule d) := by
  decide

end CheckRH

end Collatz.Arctic.RH
