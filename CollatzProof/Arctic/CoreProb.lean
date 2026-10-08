/-
Small parts of the assembly of Theorem 6.8 of the paper:
* Summing the hypothesis on the slope `κ` along an interval of an orbit (`slope_orbit`).
* Union bounds for the probability `Prσ` on the side of `σ`, and existence of a point from an event of positive probability (`Prσ_and_ge`, `exists_of_Prσ_pos`).
* Union bound for counts on a finite set (`card_inter_ge`).
-/
import CollatzProof.Arctic.CoreHyp
import CollatzProof.Arctic.ConfigLemmas

namespace Collatz.Arctic

open Classical

/-- Sum the hypothesis on the slope `κ` along an interval `n → T^m n` of an orbit whose points are all at least 2. -/
theorem slope_orbit {D : ℕ} (u : Fin D → Arc) (A : Interp D) (c : Fin D → Arc) (κ : ℕ)
    (hfin : ∀ n, 1 ≤ n → autoVal u A c n ≠ 0)
    (hslope : ∀ n, 2 ≤ n → ∀ a b : ℕ, autoVal u A c n = Arc.fin a → autoVal u A c (T n) = Arc.fin b →
      b + κ * lenT n ≤ a + κ * lenT (T n)) :
    ∀ (m n : ℕ), (∀ i < m, 2 ≤ T^[i] n) → ∀ a b : ℕ, autoVal u A c n = Arc.fin a →
      autoVal u A c (T^[m] n) = Arc.fin b → b + κ * lenT n ≤ a + κ * lenT (T^[m] n) := by
  intro m
  induction m with
  | zero =>
    intro n _ a b ha hb
    simp only [Function.iterate_zero, id] at hb
    rw [ha] at hb
    have := congrArg Arc.val hb
    simp only [Arc.val_fin] at this
    have hab : a = b := by exact_mod_cast this
    subst hab
    simp
  | succ m ih =>
    intro n horb a b ha hb
    have hn : 2 ≤ n := by simpa using horb 0 (Nat.succ_pos m)
    have hTn : 1 ≤ T n := by
      unfold T
      split_ifs <;> omega
    obtain ⟨c', hc'⟩ := (Arc.val_ne_bot_iff _).mp
      ((Arc.ne_zero_iff_val _).mp (hfin (T n) hTn))
    have h1 := hslope n hn a c' ha hc'
    have horb' : ∀ i < m, 2 ≤ T^[i] (T n) := by
      intro i hi
      have := horb (i + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    have hb' : autoVal u A c (T^[m] (T n)) = Arc.fin b := by
      rwa [← Function.iterate_succ_apply]
    have h2 := ih (T n) horb' c' b hc' hb'
    rw [Function.iterate_succ_apply]
    omega

/-- Union bound for `Prσ`: with total weight `W`, `Prσ(E₁ ∧ E₂) ≥ Prσ(E₁) + Prσ(E₂) - W`. -/
theorem Prσ_and_ge (β₀ : List Bool) (k : ℕ) (E₁ E₂ : List Bool → Prop)
    (hwt : ∀ β, 0 ≤ wtβ β) :
    Prσ β₀ k E₁ + Prσ β₀ k E₂ - (∑ β ∈ blockChoices k, wtβ β) ≤ Prσ β₀ k (fun β => E₁ β ∧ E₂ β) := by
  unfold Prσ
  have hu := Finset.sum_union_inter (s₁ := (blockChoices k).filter (fun β => E₁ (β₀ ++ β)))
    (s₂ := (blockChoices k).filter (fun β => E₂ (β₀ ++ β))) (f := wtβ)
  have hsub : (blockChoices k).filter (fun β => E₁ (β₀ ++ β)) ∪
      (blockChoices k).filter (fun β => E₂ (β₀ ++ β)) ⊆ blockChoices k :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun β _ _ => hwt β)
  have goal' : ∑ β ∈ (blockChoices k).filter (fun β => E₁ (β₀ ++ β)), wtβ β +
      ∑ β ∈ (blockChoices k).filter (fun β => E₂ (β₀ ++ β)), wtβ β - ∑ β ∈ blockChoices k, wtβ β ≤
      ∑ β ∈ (blockChoices k).filter (fun β => E₁ (β₀ ++ β)) ∩
        (blockChoices k).filter (fun β => E₂ (β₀ ++ β)), wtβ β := by linarith
  convert goal' using 2
  ext β
  simp only [Finset.mem_filter, Finset.mem_inter]
  tauto

/-- An event of positive probability is realized by a choice of `k` blocks. -/
theorem exists_of_Prσ_pos (β₀ : List Bool) (k : ℕ) (E : List Bool → Prop)
    (h : 0 < Prσ β₀ k E) : ∃ β ∈ blockChoices k, E (β₀ ++ β) := by
  unfold Prσ at h
  by_contra hc
  push Not at hc
  rw [Finset.sum_eq_zero (fun β hβ => absurd (Finset.mem_filter.mp hβ).2
    (hc β (Finset.mem_filter.mp hβ).1))] at h
  exact lt_irrefl _ h

/-- The weight of a choice of blocks is nonnegative. -/
theorem wtβ_nonneg (β : List Bool) : 0 ≤ wtβ β := by
  unfold wtβ
  apply List.prod_nonneg
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨b, -, rfl⟩ := hx
  split_ifs <;> norm_num

/-- The elements of `blockChoices k` have length `k`. -/
theorem length_of_mem_blockChoices {k : ℕ} {β : List Bool} (h : β ∈ blockChoices k) :
    β.length = k := by
  unfold blockChoices at h
  obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp h
  simp

/-- Union bound for counts on a finite set. -/
theorem card_inter_ge {α : Type*} [DecidableEq α] (X P Q : Finset α) (hP : P ⊆ X) (hQ : Q ⊆ X) :
    P.card + Q.card ≤ X.card + (P ∩ Q).card := by
  have := Finset.card_union_add_card_inter P Q
  have hu : (P ∪ Q).card ≤ X.card := Finset.card_le_card (Finset.union_subset hP hQ)
  omega

end Collatz.Arctic
