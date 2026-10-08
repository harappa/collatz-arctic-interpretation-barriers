/-
Correctness of the canonical derivation (Lemma 2.3 of the paper; the canonical-derivation lemma of Paper II): for `n ≥ 2` the list of rules `canDeriv n` gives a derivation from `can n`
to `can (T n)`.

The key lemma is the sweep `sweep_chain`: for `y ≥ 1` and `d ≤ 2`, `lft bin'(y) d R →* lft bin'(3y + d) R`
(the ternary digit `d` crosses `bin'(y)` from the low end to the high end and disappears at the left end). By induction on `y = 2y' + b`,
using `3y + d = 2(3y' + d') + b'` (`3b + d = 2d' + b'`).
-/
import CollatzProof.Arctic.Bridge

namespace Collatz.Arctic

lemma digits_two_mul_add (y b : ℕ) (hy : 1 ≤ y) (hb : b < 2) :
    Nat.digits 2 (2 * y + b) = b :: Nat.digits 2 y := by
  rw [Nat.digits_def' (by norm_num) (by omega)]
  congr 1
  · omega
  · congr 1; omega

lemma digits_two_ne_nil (y : ℕ) (hy : 1 ≤ y) : Nat.digits 2 y ≠ [] :=
  Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)

lemma binTail_eq (n : ℕ) : binTail n = ((Nat.digits 2 n).reverse.drop 1).map bitL := by
  unfold binTail bitL
  rfl

lemma binTail_two_mul_add (y b : ℕ) (hy : 1 ≤ y) (hb : b < 2) :
    binTail (2 * y + b) = binTail y ++ [bitL b] := by
  rw [binTail_eq, binTail_eq, digits_two_mul_add y b hy hb, List.reverse_cons,
    List.drop_append_of_le_length]
  · simp
  · have := digits_two_ne_nil y hy
    rw [List.length_reverse]
    exact List.length_pos_iff.mpr this

lemma tailBitsLSB_two_mul_add (y b : ℕ) (hy : 1 ≤ y) (hb : b < 2) :
    tailBitsLSB (2 * y + b) = b :: tailBitsLSB y := by
  unfold tailBitsLSB
  rw [digits_two_mul_add y b hy hb, List.reverse_cons, List.drop_append_of_le_length]
  · simp
  · have := digits_two_ne_nil y hy
    rw [List.length_reverse]
    exact List.length_pos_iff.mpr this

lemma binTail_one : binTail 1 = [] := by decide
lemma tailBitsLSB_one : tailBitsLSB 1 = [] := by decide
lemma binTail_three : binTail 3 = [Letter.t] := by decide
lemma binTail_four : binTail 4 = [Letter.f, Letter.f] := by decide
lemma binTail_five : binTail 5 = [Letter.f, Letter.t] := by decide

lemma chain_single {ρ : Rule} {u v : Word} (h : Step ρ u v) : Chain [ρ] u v :=
  Chain.cons h (Chain.nil v)

/-- The sweep: for `y ≥ 1` and `d ≤ 2`, `lft bin'(y) d R →* lft bin'(3y + d) R`. -/
theorem sweep_chain : ∀ y : ℕ, 1 ≤ y → ∀ d : ℕ, d ≤ 2 → ∀ R : Word,
    Chain (sweepRules (tailBitsLSB y) d) (Letter.lft :: (binTail y ++ digL d :: R))
      (Letter.lft :: (binTail (3 * y + d) ++ R)) := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro hy d hd R
    by_cases h1 : y = 1
    · subst h1
      rw [tailBitsLSB_one, binTail_one]
      simp only [sweepRules]
      apply chain_single
      interval_cases d
      · refine ⟨[], R, ?_, ?_⟩ <;> simp [leftRule, digL, binTail_three]
      · refine ⟨[], R, ?_, ?_⟩ <;> simp [leftRule, digL, binTail_four]
      · refine ⟨[], R, ?_, ?_⟩ <;> simp [leftRule, digL, binTail_five]
    · -- y = 2y' + b, y' ≥ 1
      set y' := y / 2 with hy'
      set b := y % 2 with hb
      have hyy : y = 2 * y' + b := by omega
      have hy'1 : 1 ≤ y' := by omega
      have hb2 : b < 2 := by omega
      have hlt : y' < y := by omega
      set d' := (3 * b + d) / 2 with hd'
      set b' := (3 * b + d) % 2 with hb'
      have hd'2 : d' ≤ 2 := by omega
      have hb'2 : b' < 2 := by omega
      rw [hyy, tailBitsLSB_two_mul_add y' b hy'1 hb2, binTail_two_mul_add y' b hy'1 hb2]
      simp only [sweepRules]
      refine Chain.cons (w := Letter.lft :: (binTail y' ++ digL d' :: bitL b' :: R)) ?_ ?_
      · refine ⟨Letter.lft :: binTail y', R, ?_, ?_⟩ <;> simp [aRule, hd', hb']
      · have h3 : 3 * (2 * y' + b) + d = 2 * (3 * y' + d') + b' := by omega
        rw [h3, binTail_two_mul_add (3 * y' + d') b' (by omega) hb'2]
        have := ih y' hlt hy'1 d' hd'2 (bitL b' :: R)
        simpa [List.append_assoc] using this

/-- Correctness of the canonical derivation (Lemma 2.3). -/
theorem canDeriv_chain (n : ℕ) (hn : 2 ≤ n) : Chain (canDeriv n) (can n) (can (T n)) := by
  set y := n / 2 with hy
  have hy1 : 1 ≤ y := by omega
  unfold canDeriv can T
  by_cases hev : n % 2 = 0
  · -- even step: `f. → .`
    have hn2 : n = 2 * y + 0 := by omega
    simp only [hev, ↓reduceIte]
    rw [hn2, binTail_two_mul_add y 0 hy1 (by norm_num)]
    have : (2 * y + 0) / 2 = y := by omega
    rw [this]
    apply chain_single
    refine ⟨Letter.lft :: binTail y, [], ?_, ?_⟩ <;> simp [bitL]
  · -- odd step: `t. → 2.` followed by the sweep
    have hn2 : n = 2 * y + 1 := by omega
    simp only [hev, ↓reduceIte]
    have hsub : (n - 1) / 2 = y := by omega
    rw [hsub]
    have hT : (3 * n + 1) / 2 = 3 * y + 2 := by omega
    rw [hT]
    rw [hn2, binTail_two_mul_add y 1 hy1 (by norm_num)]
    refine Chain.cons (w := Letter.lft :: (binTail y ++ digL 2 :: [Letter.rgt])) ?_ ?_
    · refine ⟨Letter.lft :: binTail y, [], ?_, ?_⟩ <;> simp [bitL, digL]
    · exact sweep_chain y hy1 2 (le_refl 2) [Letter.rgt]

end Collatz.Arctic
