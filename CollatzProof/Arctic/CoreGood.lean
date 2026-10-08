/-
Assembly of Theorem 6.8 of the paper: existence of free bits that satisfy the four events (E1)–(E4) on the side of `t` simultaneously.
The configuration at the starting point is minimal (probability at least `2^{-L}`), the windows of the free bits (`M'` intervals, each failing with probability at most `ε_w`),
the lower bound at the end point (failure at most `η`), and an occurrence of the absorbing word at the end point (failure at most `ε_a`). If the failure probabilities add up to less than `2^{-L}`, the events intersect.
-/
import CollatzProof.Arctic.CoreU

namespace Collatz.Arctic

theorem exists_good_x (F L M' : ℕ) (E1 E3 E4 : ℕ → Prop) (E2 : ℕ → ℕ → Prop)
    [DecidablePred E1] [DecidablePred E3] [DecidablePred E4] [∀ t, DecidablePred (E2 t)]
    (hLF : L ≤ F) (εw εa η : ℝ)
    (h1 : (2 : ℝ) ^ (F - L) ≤ (((Finset.range (2 ^ F)).filter E1).card : ℝ))
    (h2 : ∀ t < M', (((Finset.range (2 ^ F)).filter (fun x => ¬ E2 t x)).card : ℝ) ≤ εw * 2 ^ F)
    (h3 : (1 - η) * 2 ^ F ≤ (((Finset.range (2 ^ F)).filter E3).card : ℝ))
    (h4 : (((Finset.range (2 ^ F)).filter (fun x => ¬ E4 x)).card : ℝ) ≤ εa * 2 ^ F)
    (hsmall : M' * εw + η + εa < 1 / 2 ^ L) :
    ∃ x < 2 ^ F, E1 x ∧ (∀ t < M', E2 t x) ∧ E3 x ∧ E4 x := by
  classical
  by_contra hno
  push Not at hno
  set X := Finset.range (2 ^ F) with hX
  -- every point fails some event
  have hcover : X ⊆ X.filter (fun x => ¬ E1 x) ∪
      ((Finset.range M').biUnion (fun t => X.filter (fun x => ¬ E2 t x)) ∪
        (X.filter (fun x => ¬ E3 x) ∪ X.filter (fun x => ¬ E4 x))) := by
    intro x hx
    have hx' := Finset.mem_range.mp hx
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range]
    by_cases e1 : E1 x
    · by_cases e2 : ∀ t < M', E2 t x
      · by_cases e3 : E3 x
        · exact Or.inr (Or.inr (Or.inr ⟨hx, hno x hx' e1 e2 e3⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨hx, e3⟩))
      · push Not at e2
        obtain ⟨t, ht, ht'⟩ := e2
        exact Or.inr (Or.inl ⟨t, ht, hx, ht'⟩)
    · exact Or.inl ⟨hx, e1⟩
  have hc := Finset.card_le_card hcover
  have hc1 := Finset.card_union_le (X.filter (fun x => ¬ E1 x))
    ((Finset.range M').biUnion (fun t => X.filter (fun x => ¬ E2 t x)) ∪
      (X.filter (fun x => ¬ E3 x) ∪ X.filter (fun x => ¬ E4 x)))
  have hc2 := Finset.card_union_le ((Finset.range M').biUnion (fun t => X.filter (fun x => ¬ E2 t x)))
    (X.filter (fun x => ¬ E3 x) ∪ X.filter (fun x => ¬ E4 x))
  have hc3 := Finset.card_union_le (X.filter (fun x => ¬ E3 x)) (X.filter (fun x => ¬ E4 x))
  have hc4 := Finset.card_biUnion_le (s := Finset.range M') (t := fun t => X.filter (fun x => ¬ E2 t x))
  -- sizes of the complements
  have hn1 := Finset.card_filter_add_card_filter_not (s := X) E1
  have hn3 := Finset.card_filter_add_card_filter_not (s := X) E3
  have hXc : (X.card : ℝ) = 2 ^ F := by rw [hX, Finset.card_range]; push_cast; ring
  have hsum : ((∑ t ∈ Finset.range M', (X.filter (fun x => ¬ E2 t x)).card : ℕ) : ℝ) ≤ M' * (εw * 2 ^ F) := by
    push_cast
    calc ∑ t ∈ Finset.range M', ((X.filter (fun x => ¬ E2 t x)).card : ℝ)
        ≤ ∑ t ∈ Finset.range M', εw * 2 ^ F :=
          Finset.sum_le_sum (fun t ht => h2 t (Finset.mem_range.mp ht))
      _ = M' * (εw * 2 ^ F) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hall : (X.card : ℝ) ≤ ((X.filter (fun x => ¬ E1 x)).card : ℝ) +
      (((∑ t ∈ Finset.range M', (X.filter (fun x => ¬ E2 t x)).card : ℕ) : ℝ) +
        (((X.filter (fun x => ¬ E3 x)).card : ℝ) + ((X.filter (fun x => ¬ E4 x)).card : ℝ))) := by
    have : X.card ≤ (X.filter (fun x => ¬ E1 x)).card +
        ((∑ t ∈ Finset.range M', (X.filter (fun x => ¬ E2 t x)).card) +
          ((X.filter (fun x => ¬ E3 x)).card + (X.filter (fun x => ¬ E4 x)).card)) := by omega
    exact_mod_cast this
  have hn1' : ((X.filter (fun x => ¬ E1 x)).card : ℝ) = 2 ^ F - ((X.filter E1).card : ℝ) := by
    have : ((X.filter E1).card : ℝ) + ((X.filter (fun x => ¬ E1 x)).card : ℝ) = X.card := by
      exact_mod_cast hn1
    linarith
  have hn3' : ((X.filter (fun x => ¬ E3 x)).card : ℝ) = 2 ^ F - ((X.filter E3).card : ℝ) := by
    have : ((X.filter E3).card : ℝ) + ((X.filter (fun x => ¬ E3 x)).card : ℝ) = X.card := by
      exact_mod_cast hn3
    linarith
  have hpow : (2 : ℝ) ^ (F - L) = 2 ^ F * (1 / 2 ^ L) := by
    rw [show F = (F - L) + L from (Nat.sub_add_cancel hLF).symm, pow_add]
    field_simp
    rw [Nat.add_sub_cancel]
  have h2F : (0 : ℝ) < 2 ^ F := by positivity
  have := mul_lt_mul_of_pos_left hsmall h2F
  nlinarith

end Collatz.Arctic
