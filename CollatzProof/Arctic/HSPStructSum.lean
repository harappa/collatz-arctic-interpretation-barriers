/-
Sums over the joined words (a step of the proof of `MinRate` in the general case: Theorem B.3, Step 6, (J2) and (J3)).

* `PS n`: the set of all lists of `n` pairs (a realized permutation and a word of length `L`). `hsp_PS_sum`: the pairs can be summed out one at a time.
* **Sum identity for the variance** `hsp_sV_var`: `Σ_{x₀, ps ∈ PS n} pvar (sV x₀ ps) = (n+1) (|G| 2^L)^n Σ_x pvar (a_x)`
  (averaging over the junction permutations removes the cross terms, `hsp_pvar_avg`).
* `hsp_count_notGood`: the number of joined words containing a segment that is not good. `hsp_word_sum`: the sum of a nonnegative function over the joined words
  is bounded by sums over uniform words (the subsets with fixed junction words).
-/
import CollatzProof.Arctic.HSPStruct
import CollatzProof.Arctic.HSPVarAlg

namespace Collatz.Arctic

open MinIdeal Matrix Arc Classical

variable {D : ℕ} {A : Interp D} {C : Finset (Fin D)} (S : LinSetup A C) (h L : ℕ)

/-- The set of all lists of `n` pairs. -/
noncomputable def PS : ℕ → Finset (PList S)
  | 0 => {[]}
  | n + 1 => ((PS n) ×ˢ (realSet S ×ˢ wordsOfLen L)).image (fun pq => pq.2 :: pq.1)

lemma hsp_PS_sum (n : ℕ) (F : PList S → ℝ) :
    ∑ ps ∈ PS S L (n + 1), F ps = ∑ ps ∈ PS S L n, ∑ g ∈ realSet S, ∑ x ∈ wordsOfLen L, F ((g, x) :: ps) := by
  rw [PS, Finset.sum_image]
  · rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun ps _ => ?_)
    rw [Finset.sum_product]
  · intro a _ b _ hab
    simp only [List.cons.injEq] at hab
    exact Prod.ext hab.2 hab.1

lemma hsp_PS_card : ∀ n : ℕ, ((PS S L n).card : ℝ) = ((realSet S).card * 2 ^ L : ℝ) ^ n
  | 0 => by simp [PS]
  | n + 1 => by
    have h1 := hsp_PS_sum S L n (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, WinLLN.card_words] at h1
    rw [h1, hsp_PS_card n]
    push_cast; ring

lemma hsp_PS_mem : ∀ {n : ℕ} {ps : PList S}, ps ∈ PS S L n →
    ps.length = n ∧ ∀ gx ∈ ps, gx.1 ∈ realSet S ∧ gx.2 ∈ wordsOfLen L
  | 0, ps, hps => by
    simp only [PS, Finset.mem_singleton] at hps
    subst hps; simp
  | n + 1, ps, hps => by
    simp only [PS, Finset.mem_image, Finset.mem_product] at hps
    obtain ⟨⟨ps', g, x⟩, ⟨hps', hg, hx⟩, rfl⟩ := hps
    obtain ⟨h1, h2⟩ := hsp_PS_mem hps'
    refine ⟨by simp [h1], fun gx hgx => ?_⟩
    rcases List.mem_cons.mp hgx with rfl | hgx
    · exact ⟨hg, hx⟩
    · exact h2 gx hgx

lemma hsp_PS_allOk {n : ℕ} {x₀ : Word} (hx₀ : x₀ ∈ wordsOfLen L) {ps : PList S}
    (hps : ps ∈ PS S L n) : AllOk S x₀ ps := by
  refine ⟨WinLLN.bin_of_mem hx₀, fun gx hgx => ?_⟩
  obtain ⟨h1, h2⟩ := (hsp_PS_mem S L hps).2 gx hgx
  exact ⟨WinLLN.bin_of_mem h2, (hsp_mem_realSet S).mp h1⟩

/-- **Sum identity for the variance**. -/
theorem hsp_sV_var (hSC : StrongConnIn A C) : ∀ n : ℕ,
    ∑ x₀ ∈ wordsOfLen L, ∑ ps ∈ PS S L n, pvar (sV S h x₀ ps) =
      (n + 1) * ((realSet S).card * 2 ^ L : ℝ) ^ n *
        ∑ x ∈ wordsOfLen L, pvar (prof S (segDec S h x).2.1)
  | 0 => by simp [PS, sV]
  | n + 1 => by
    have ih := hsp_sV_var hSC n
    have hstep : ∀ x₀ ps, ∑ g ∈ realSet S, ∑ x ∈ wordsOfLen L, pvar (sV S h x₀ ((g, x) :: ps)) =
        ∑ x ∈ wordsOfLen L, (realSet S).card *
          (pvar (sV S h x₀ ps) + pvar (prof S (segDec S h x).2.1)) := by
      intro x₀ ps
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      exact hsp_pvar_avg (realSet S) (hsp_card_fiber S hSC) (sV S h x₀ ps)
        (prof S (segDec S h x).2.1) (wPerm S (segDec S h x).1)
        ((wPerm S (sK S h x₀ ps)).trans (wPerm S (sQ S h x₀ ps)))
    have hL : ∑ x₀ ∈ wordsOfLen L, ∑ ps ∈ PS S L (n + 1), pvar (sV S h x₀ ps) =
        ∑ x₀ ∈ wordsOfLen L, ∑ ps ∈ PS S L n, ∑ x ∈ wordsOfLen L, ((realSet S).card *
          pvar (sV S h x₀ ps) + (realSet S).card * pvar (prof S (segDec S h x).2.1)) := by
      refine Finset.sum_congr rfl (fun x₀ _ => ?_)
      rw [hsp_PS_sum]
      refine Finset.sum_congr rfl (fun ps _ => ?_)
      rw [hstep]
      simp only [mul_add]
    rw [hL]
    simp only [Finset.sum_add_distrib]
    have e1 : ∑ x₀ ∈ wordsOfLen L, ∑ ps ∈ PS S L n, ∑ _x ∈ wordsOfLen L,
        ((realSet S).card : ℝ) * pvar (sV S h x₀ ps) =
        (realSet S).card * 2 ^ L * ∑ x₀ ∈ wordsOfLen L, ∑ ps ∈ PS S L n, pvar (sV S h x₀ ps) := by
      simp only [Finset.sum_const, WinLLN.card_words, nsmul_eq_mul, Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
    have e2 : ∑ x₀ ∈ wordsOfLen L, ∑ ps ∈ PS S L n, ∑ x ∈ wordsOfLen L,
        ((realSet S).card : ℝ) * pvar (prof S (segDec S h x).2.1) =
        2 ^ L * ((realSet S).card * 2 ^ L : ℝ) ^ n * (realSet S).card *
          ∑ x ∈ wordsOfLen L, pvar (prof S (segDec S h x).2.1) := by
      rw [← Finset.mul_sum]
      simp only [Finset.sum_const, WinLLN.card_words, nsmul_eq_mul]
      rw [hsp_PS_card]
      push_cast; ring
    rw [e1, e2, ih]
    push_cast; ring

/-- The number of joined words containing a segment that is not good. -/
theorem hsp_count_notGood : ∀ n : ℕ,
    ∑ x₀ ∈ wordsOfLen L, ∑ ps ∈ PS S L n, (if AllGood S h x₀ ps then (0 : ℝ) else 1) ≤
      (n + 1) * ((realSet S).card * 2 ^ L : ℝ) ^ n *
        (((wordsOfLen L).filter (fun x => ¬ GoodSeg S h x)).card : ℝ)
  | 0 => by
    simp only [PS, Finset.sum_singleton, AllGood, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
    simp
  | n + 1 => by
    have ih := hsp_count_notGood n
    have hpt : ∀ x₀ ps g x, (if AllGood S h x₀ ((g, x) :: ps) then (0 : ℝ) else 1) ≤
        (if AllGood S h x₀ ps then (0 : ℝ) else 1) + (if GoodSeg S h x then (0 : ℝ) else 1) := by
      intro x₀ ps g x
      by_cases h1 : AllGood S h x₀ ps
      · by_cases h2 : GoodSeg S h x
        · have : AllGood S h x₀ ((g, x) :: ps) := ⟨h1.1, fun gx hgx => by
            rcases List.mem_cons.mp hgx with rfl | hgx
            · exact h2
            · exact h1.2 gx hgx⟩
          simp [this, h1, h2]
        · split_ifs <;> norm_num
      · split_ifs <;> norm_num
    set B : ℝ := (((wordsOfLen L).filter (fun x => ¬ GoodSeg S h x)).card : ℝ) with hB
    set G : ℝ := ((realSet S).card : ℝ) with hG
    have e : ∑ x ∈ wordsOfLen L, (if GoodSeg S h x then (0 : ℝ) else 1) = B := by
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hin : ∀ x₀ ps, ∑ g ∈ realSet S, ∑ x ∈ wordsOfLen L,
        ((if AllGood S h x₀ ps then (0 : ℝ) else 1) + (if GoodSeg S h x then (0 : ℝ) else 1)) =
        G * 2 ^ L * (if AllGood S h x₀ ps then (0 : ℝ) else 1) + G * B := by
      intro x₀ ps
      simp only [Finset.sum_add_distrib, Finset.sum_const, WinLLN.card_words, nsmul_eq_mul, e]
      push_cast; ring
    have h1 : ∑ x₀ ∈ wordsOfLen L, ∑ ps ∈ PS S L (n + 1), (if AllGood S h x₀ ps then (0 : ℝ) else 1)
        ≤ ∑ x₀ ∈ wordsOfLen L, ∑ ps ∈ PS S L n,
          (G * 2 ^ L * (if AllGood S h x₀ ps then (0 : ℝ) else 1) + G * B) := by
      refine Finset.sum_le_sum (fun x₀ _ => ?_)
      rw [hsp_PS_sum]
      refine Finset.sum_le_sum (fun ps _ => ?_)
      rw [← hin]
      exact Finset.sum_le_sum (fun g _ => Finset.sum_le_sum (fun x _ => hpt x₀ ps g x))
    have h2 : ∑ x₀ ∈ wordsOfLen L, ∑ ps ∈ PS S L n,
        (G * 2 ^ L * (if AllGood S h x₀ ps then (0 : ℝ) else 1) + G * B) =
        G * 2 ^ L * (∑ x₀ ∈ wordsOfLen L, ∑ ps ∈ PS S L n, (if AllGood S h x₀ ps then (0 : ℝ) else 1))
          + G * B * 2 ^ L * (G * 2 ^ L) ^ n := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, WinLLN.card_words, nsmul_eq_mul,
        Finset.mul_sum]
      rw [hsp_PS_card]
      push_cast; ring
    rw [h2] at h1
    have hG0 : 0 ≤ G * 2 ^ L := by positivity
    have h3 := mul_le_mul_of_nonneg_left ih hG0
    refine h1.trans ?_
    have e3 : (↑(n + 1) + 1) * (G * 2 ^ L) ^ (n + 1) * B =
        G * 2 ^ L * ((n + 1) * (G * 2 ^ L) ^ n * B) + G * B * 2 ^ L * (G * 2 ^ L) ^ n := by
      push_cast; ring
    rw [e3]
    linarith

/-- Inserting a fixed word `j` between words: `Σ_{W ∈ words N} Σ_{x ∈ words L} F(W j x) ≤ Σ_{W' ∈ words (N + |j| + L)} F W'`. -/
lemma hsp_sum_insert (F : Word → ℝ) (hF : ∀ W, 0 ≤ F W) {j : Word} (hj : IsDigits j) (N : ℕ) :
    ∑ W ∈ wordsOfLen N, ∑ x ∈ wordsOfLen L, F (W ++ j ++ x) ≤
      ∑ W' ∈ wordsOfLen (N + (j.length + L)), F W' := by
  have e1 : ∑ W' ∈ wordsOfLen (N + (j.length + L)), F W' =
      ∑ W ∈ wordsOfLen N, ∑ V ∈ wordsOfLen (j.length + L), F (W ++ V) := by
    rw [← hsp_sum_append N (j.length + L) (fun u v => F (u ++ v))]
    simp only [List.take_append_drop]
  rw [e1]
  refine Finset.sum_le_sum (fun W _ => ?_)
  have e2 : ∑ V ∈ wordsOfLen (j.length + L), F (W ++ V) =
      ∑ j' ∈ wordsOfLen j.length, ∑ x ∈ wordsOfLen L, F (W ++ (j' ++ x)) := by
    rw [← hsp_sum_append j.length L (fun u v => F (W ++ (u ++ v)))]
    simp only [List.take_append_drop]
  rw [e2]
  have hjm : j ∈ wordsOfLen j.length := mem_wordsOfLen_of rfl hj
  have := Finset.single_le_sum (f := fun j' => ∑ x ∈ wordsOfLen L, F (W ++ (j' ++ x)))
    (fun j' _ => Finset.sum_nonneg (fun x _ => hF _)) hjm
  simpa [List.append_assoc] using this

/-- **Sum over the joined words**: if a nonnegative `F` satisfies `Σ F ≤ δ 2^(N + c)` over uniform words of length `N ≥ N₀`, and `N₀ ≤ L`, then
the sum over the joined words is at most `δ |G|^n 2^((n+1)L + n·jwMax + c)`. -/
theorem hsp_word_sum (N₀ : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (hL : N₀ ≤ L) : ∀ (n : ℕ) (F : Word → ℝ) (c : ℕ),
    (∀ W, 0 ≤ F W) → (∀ N, N₀ ≤ N → ∑ W ∈ wordsOfLen N, F W ≤ δ * 2 ^ (N + c)) →
    ∑ x₀ ∈ wordsOfLen L, ∑ ps ∈ PS S L n, F (sWord S x₀ ps) ≤
      δ * ((realSet S).card : ℝ) ^ n * 2 ^ ((n + 1) * L + n * jwMax S + c)
  | 0, F, c, _, hb => by
    simp only [PS, Finset.sum_singleton, sWord, pow_zero, mul_one]
    simpa using hb L hL
  | n + 1, F, c, hF, hb => by
    -- `F_g W := Σ_x F(W jw(g) x)`
    set Fg : Equiv.Perm (Cls S.E S.hE) → Word → ℝ :=
      fun g W => ∑ x ∈ wordsOfLen L, F (W ++ jw S g ++ x) with hFg
    have hFg0 : ∀ g W, 0 ≤ Fg g W := fun g W => Finset.sum_nonneg (fun x _ => hF _)
    have hFgb : ∀ g ∈ realSet S, ∀ N, N₀ ≤ N →
        ∑ W ∈ wordsOfLen N, Fg g W ≤ δ * 2 ^ (N + (jwMax S + L + c)) := by
      intro g hg N hN
      have h1 := hsp_sum_insert L F hF (hsp_jw_digits S g) N
      have h2 := hb (N + ((jw S g).length + L)) (by omega)
      have h3 : (2 : ℝ) ^ (N + ((jw S g).length + L) + c) ≤ 2 ^ (N + (jwMax S + L + c)) :=
        pow_le_pow_right₀ (by norm_num) (by have := hsp_jw_le S hg; omega)
      have h4 := mul_le_mul_of_nonneg_left h3 hδ
      simp only [hFg]
      linarith
    have ih : ∀ g ∈ realSet S, ∑ x₀ ∈ wordsOfLen L, ∑ ps ∈ PS S L n, Fg g (sWord S x₀ ps) ≤
        δ * ((realSet S).card : ℝ) ^ n * 2 ^ ((n + 1) * L + n * jwMax S + (jwMax S + L + c)) :=
      fun g hg => hsp_word_sum N₀ δ hδ hL n (Fg g) (jwMax S + L + c) (hFg0 g) (hFgb g hg)
    have e1 : ∑ x₀ ∈ wordsOfLen L, ∑ ps ∈ PS S L (n + 1), F (sWord S x₀ ps) =
        ∑ x₀ ∈ wordsOfLen L, ∑ g ∈ realSet S, ∑ ps ∈ PS S L n, Fg g (sWord S x₀ ps) := by
      refine Finset.sum_congr rfl (fun x₀ _ => ?_)
      rw [hsp_PS_sum]
      rw [Finset.sum_comm (s := PS S L n) (t := realSet S)]
      rfl
    rw [e1, Finset.sum_comm (s := wordsOfLen L) (t := realSet S)]
    calc ∑ g ∈ realSet S, ∑ x₀ ∈ wordsOfLen L, ∑ ps ∈ PS S L n, Fg g (sWord S x₀ ps)
        ≤ ∑ _g ∈ realSet S, δ * ((realSet S).card : ℝ) ^ n *
            2 ^ ((n + 1) * L + n * jwMax S + (jwMax S + L + c)) := Finset.sum_le_sum ih
      _ = δ * ((realSet S).card : ℝ) ^ (n + 1) * 2 ^ ((n + 1 + 1) * L + (n + 1) * jwMax S + c) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have : (n + 1) * L + n * jwMax S + (jwMax S + L + c) =
            (n + 1 + 1) * L + (n + 1) * jwMax S + c := by ring
        rw [this, pow_succ]
        ring

end Collatz.Arctic
