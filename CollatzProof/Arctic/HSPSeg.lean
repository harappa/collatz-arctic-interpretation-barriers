/-
Junction words and the decomposition of segments (a step of the proof of `MinRate` in the general case: Theorem B.3, Step 6).

* **Junction word** `jw S g := u ++ jy S g ++ u`: for each realized permutation `g` we choose a digit word `jy S g` whose permutation is `g`.
* **Good segment** `GoodSeg S h x`: `x = p u c u q` with `|p|, |q| ≤ h`. Decomposition `segP`, `segC`, `segQ` (`([], x, [])` if `x` is not good).
  The fraction of words of length `L` that are not good is at most `2 (1 - 2^{-|u|})^{⌊h/|u|⌋}` (`hsp_card_not_good`, `card_noOcc_le`).
-/
import CollatzProof.Arctic.HSPLinVal
import CollatzProof.Arctic.WindowLLN3

namespace Collatz.Arctic

open MinIdeal Matrix Arc

variable {D : ℕ} {A : Interp D} {C : Finset (Fin D)} (S : LinSetup A C)

/-! ### Junction words -/

/-- A digit word realizing the permutation `g` (empty if `g` is not realized). -/
noncomputable def jy (g : Equiv.Perm (Cls S.E S.hE)) : Word := by
  classical exact if h : realized S g then Classical.choose h else []

lemma hsp_jy_spec {g : Equiv.Perm (Cls S.E S.hE)} (hg : realized S g) :
    IsDigits (jy S g) ∧ ∀ i, g i = piX S.hE (suppRel (ev (restrictI C A) (jy S g))) i := by
  classical
  unfold jy
  simp only [hg, ↓reduceDIte]
  exact Classical.choose_spec hg

lemma hsp_jy_digits (g : Equiv.Perm (Cls S.E S.hE)) : IsDigits (jy S g) := by
  classical
  by_cases hg : realized S g
  · exact (hsp_jy_spec S hg).1
  · unfold jy; simp only [hg, ↓reduceDIte]; intro s hs; simp at hs

/-- The junction word `u ++ jy g ++ u`. -/
noncomputable def jw (g : Equiv.Perm (Cls S.E S.hE)) : Word := S.u ++ jy S g ++ S.u

lemma hsp_jw_digits (g : Equiv.Perm (Cls S.E S.hE)) : IsDigits (jw S g) :=
  hsp_isDigits_append (hsp_isDigits_append S.hu (hsp_jy_digits S g)) S.hu

/-- An upper bound on the lengths of the junction words (the maximum over the realized permutations). -/
noncomputable def jwMax : ℕ := (realSet S).sup (fun g => (jw S g).length)

lemma hsp_jw_le {g : Equiv.Perm (Cls S.E S.hE)} (hg : g ∈ realSet S) : (jw S g).length ≤ jwMax S :=
  Finset.le_sup (f := fun g => (jw S g).length) hg

/-- The permutation of the word `q ++ jw g ++ p` with a junction word in the middle is `π_p ∘ g ∘ π_q`. -/
lemma hsp_piX_junction {g : Equiv.Perm (Cls S.E S.hE)} (hg : realized S g) {p q : Word}
    (hp : IsDigits p) (hq : IsDigits q) (i : Cls S.E S.hE) :
    piX S.hE (suppRel (ev (restrictI C A) (q ++ jw S g ++ p))) i =
      piX S.hE (suppRel (ev (restrictI C A) p))
        (g (piX S.hE (suppRel (ev (restrictI C A) q)) i)) := by
  obtain ⟨hyd, hyg⟩ := hsp_jy_spec S hg
  have e : q ++ jw S g ++ p = (q ++ S.u ++ jy S g) ++ S.u ++ p := by
    simp [jw, List.append_assoc]
  rw [e, hsp_piX_word S (hsp_isDigits_append (hsp_isDigits_append hq S.hu) hyd) hp,
    hsp_piX_word S hq hyd, hyg]

/-! ### Decomposition of words -/

lemma hsp_split3 (w : Word) {a b : ℕ} (hab : a ≤ b) :
    w = w.take a ++ window w a (b - a) ++ w.drop b := by
  have h1 : w.drop a = (w.drop a).take (b - a) ++ w.drop b := by
    conv_lhs => rw [← List.take_append_drop (b - a) (w.drop a)]
    rw [List.drop_drop, Nat.add_sub_cancel' hab]
  calc w = w.take a ++ w.drop a := (List.take_append_drop a w).symm
    _ = _ := by rw [h1, window, List.append_assoc]

/-- Between two occurrences: `window w i₁ (i₂ + |z| - i₁) = z ++ x ++ z`. -/
lemma hsp_window_zxz (w z : Word) {i₁ i₂ : ℕ} (h12 : i₁ + z.length ≤ i₂)
    (h1 : window w i₁ z.length = z) (h2 : window w i₂ z.length = z) :
    window w i₁ (i₂ + z.length - i₁) =
      z ++ window w (i₁ + z.length) (i₂ - i₁ - z.length) ++ z := by
  have e : i₂ + z.length - i₁ = z.length + ((i₂ - i₁ - z.length) + z.length) := by omega
  rw [e, window_add, window_add, h1, show i₁ + z.length + (i₂ - i₁ - z.length) = i₂ by omega, h2,
    List.append_assoc]

/-! ### Good segments -/

/-- A good segment: `x = p u c u q` with `|p|, |q| ≤ h`. -/
def GoodSeg (h : ℕ) (x : Word) : Prop :=
  ∃ p c q : Word, x = p ++ S.u ++ c ++ S.u ++ q ∧ p.length ≤ h ∧ q.length ≤ h

/-- The decomposition of a segment (`([], x, [])` if it is not good). -/
noncomputable def segDec (h : ℕ) (x : Word) : Word × Word × Word := by
  classical exact if hx : GoodSeg S h x then
    (Classical.choose hx, Classical.choose (Classical.choose_spec hx),
      Classical.choose (Classical.choose_spec (Classical.choose_spec hx)))
    else ([], x, [])

lemma hsp_segDec_good {h : ℕ} {x : Word} (hx : GoodSeg S h x) :
    x = (segDec S h x).1 ++ S.u ++ (segDec S h x).2.1 ++ S.u ++ (segDec S h x).2.2 ∧
      (segDec S h x).1.length ≤ h ∧ (segDec S h x).2.2.length ≤ h := by
  classical
  unfold segDec
  simp only [hx, ↓reduceDIte]
  exact Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hx))

lemma hsp_segDec_len (h : ℕ) (x : Word) :
    (segDec S h x).1.length ≤ h ∧ (segDec S h x).2.2.length ≤ h ∧ (segDec S h x).2.1.length ≤ x.length := by
  classical
  by_cases hx : GoodSeg S h x
  · obtain ⟨e, h1, h2⟩ := hsp_segDec_good S hx
    refine ⟨h1, h2, ?_⟩
    conv_rhs => rw [e]
    simp only [List.length_append]
    omega
  · unfold segDec; simp only [hx, ↓reduceDIte]; simp

lemma hsp_segDec_digits (h : ℕ) {x : Word} (hx : IsDigits x) :
    IsDigits (segDec S h x).1 ∧ IsDigits (segDec S h x).2.1 ∧ IsDigits (segDec S h x).2.2 := by
  classical
  by_cases hg : GoodSeg S h x
  · obtain ⟨e, -, -⟩ := hsp_segDec_good S hg
    rw [e] at hx
    refine ⟨fun s hs => hx s ?_, fun s hs => hx s ?_, fun s hs => hx s ?_⟩ <;> simp [hs]
  · unfold segDec; simp only [hg, ↓reduceDIte]
    refine ⟨fun s hs => by simp at hs, hx, fun s hs => by simp at hs⟩

/-! ### Few segments are not good -/

open Classical in
/-- A word of length `L` in which `u` occurs both in `[0, h)` and in `[L - h, L)` is a good segment (`2h ≤ L`). The number of words that are not good
is at most `2 · 2^L (1 - 2^{-|u|})^{⌊h/|u|⌋}`. -/
theorem hsp_card_not_good (L h : ℕ) (hh : 2 * h ≤ L) :
    ((((wordsOfLen L).filter (fun x => ¬ GoodSeg S h x)).card : ℕ) : ℚ) ≤
      2 * (2 ^ L * (1 - 1 / 2 ^ S.u.length) ^ (h / S.u.length)) := by
  set U := S.u.length
  set B1 : Word → Prop := fun w => ∀ i, 0 ≤ i → i + U ≤ h → window w i U ≠ S.u with hB1
  set B2 : Word → Prop := fun w => ∀ i, L - h ≤ i → i + U ≤ L → window w i U ≠ S.u with hB2
  have hsub : (wordsOfLen L).filter (fun x => ¬ GoodSeg S h x) ⊆
      (wordsOfLen L).filter B1 ∪ (wordsOfLen L).filter B2 := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    have h1 := h1 hx.1
    have h2 := h2 hx.1
    simp only [hB1, hB2, not_forall, not_not] at h1 h2
    obtain ⟨i₁, -, hi₁, hw₁⟩ := h1
    obtain ⟨i₂, hi₂, hi₂L, hw₂⟩ := h2
    have hxl := length_of_mem_wordsOfLen hx.1
    apply hx.2
    have h12 : i₁ + U ≤ i₂ := by omega
    have hmid := hsp_window_zxz x S.u h12 hw₁ hw₂
    have hsplit := hsp_split3 x (a := i₁) (b := i₂ + U) (by omega)
    rw [hmid] at hsplit
    refine ⟨x.take i₁, window x (i₁ + U) (i₂ - i₁ - U), x.drop (i₂ + U), ?_, ?_, ?_⟩
    · conv_lhs => rw [hsplit]
      simp only [List.append_assoc]
      rfl
    · rw [List.length_take]; omega
    · rw [List.length_drop]; omega
  have hzw : S.u ∈ wordsOfLen S.u.length := mem_wordsOfLen_of rfl S.hu
  have hc1 := card_noOcc_le L 0 h hzw (by omega)
  have hc2 := card_noOcc_le L (L - h) L hzw le_rfl
  rw [Nat.sub_zero] at hc1
  rw [show L - (L - h) = h by omega] at hc2
  have h3 := Finset.card_le_card hsub
  have h4 := Finset.card_union_le ((wordsOfLen L).filter B1) ((wordsOfLen L).filter B2)
  have h5 : ((((wordsOfLen L).filter (fun x => ¬ GoodSeg S h x)).card : ℕ) : ℚ) ≤
      (((wordsOfLen L).filter B1).card : ℚ) + (((wordsOfLen L).filter B2).card : ℚ) := by
    exact_mod_cast h3.trans h4
  linarith

end Collatz.Arctic
