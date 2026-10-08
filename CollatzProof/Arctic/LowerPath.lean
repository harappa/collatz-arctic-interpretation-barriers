/-
Parts of the Lean proof of Lemma 6.6 of the paper (lower bound for a sequence of concatenated close-to-uniform intervals, Section 6.3).
This file contains the deterministic lemmas on paths and restricted processes. Lineages and stages are in
`LowerLineage.lean`, the counting in `LowerCount.lean`, and the main theorem in `Lower.lean`.

* Lemmas on arctic values (extracting finite values, decomposing finite entries of matrix products), concatenation of digit words.
* The product restricted to a component, `ev (restrictI C A) w`: it is at most the original product (`ev_restrict_le`), and the end index of a finite entry lies in `C`
  (`ev_restrict_mem`).
* A path reading a digit word between two points of a set that is convex for paths (it contains the points of the paths between two of its points) stays in the set
  (`ev_restrict_ne_zero`). The component `C(i)` is convex (`pathConvex_comp`) and strongly connected (`strongConn_comp`, the premise of `HSP`).
* Good words `SPGood`: words for which the conclusion of `HSP` holds simultaneously for all `(C, S)` satisfying the premise.
* If the process never dies from a set of starting indices, it never dies from the support after reading a word either (`neverDies_after`).
* Bounding the value vector from below by the weight of one path (`vec_step`; the weights are nonnegative, so values do not decrease).
-/
import CollatzProof.Arctic.ConfigLemmas
import CollatzProof.Arctic.CoreHyp

namespace Collatz.Arctic.Lower

open MinIdeal Matrix

variable {D : ℕ}

/-! ### Lemmas on arctic values -/

lemma arc_one_ne_zero : (1 : Arc) ≠ 0 := by
  rw [Arc.ne_zero_iff_val]; simp

lemma arc_zero_le (a : Arc) : (0 : Arc) ≤ a := by
  rw [Arc.le_iff_val]; simp

lemma arc_exists_fin {a : Arc} (h : a ≠ 0) : ∃ v : ℕ, a = Arc.fin v :=
  (Arc.val_ne_bot_iff a).mp ((Arc.ne_zero_iff_val a).mp h)

lemma arc_exists_of_fin_le {a : Arc} {x : ℕ} (h : Arc.fin x ≤ a) : ∃ v : ℕ, a = Arc.fin v ∧ x ≤ v := by
  have hne : a ≠ 0 := by
    intro h0
    rw [h0, Arc.le_iff_val] at h
    simp at h
  obtain ⟨v, rfl⟩ := arc_exists_fin hne
  exact ⟨v, rfl, Arc.fin_le_fin.mp h⟩

lemma one_apply_self_ne_zero (a : Fin D) : (1 : AMat D) a a ≠ 0 := by
  rw [Matrix.one_apply_eq]; exact arc_one_ne_zero

lemma mul_apply_ne_zero_iff (M N : AMat D) (i j : Fin D) :
    (M * N) i j ≠ 0 ↔ ∃ k, M i k ≠ 0 ∧ N k j ≠ 0 := by
  rw [Matrix.mul_apply, Arc.sum_ne_zero_iff]
  simp only [Finset.mem_univ, true_and, Arc.mul_ne_zero_iff]

lemma isDigits_append {w₁ w₂ : Word} (h₁ : IsDigits w₁) (h₂ : IsDigits w₂) : IsDigits (w₁ ++ w₂) := by
  intro s hs
  rcases List.mem_append.mp hs with h | h
  · exact h₁ s h
  · exact h₂ s h

lemma isDigits_of_append_left {w₁ w₂ : Word} (h : IsDigits (w₁ ++ w₂)) : IsDigits w₁ :=
  fun s hs => h s (List.mem_append_left _ hs)

lemma isDigits_of_append_right {w₁ w₂ : Word} (h : IsDigits (w₁ ++ w₂)) : IsDigits w₂ :=
  fun s hs => h s (List.mem_append_right _ hs)

/-! ### Restricted products -/

lemma restrictI_le (C : Finset (Fin D)) (A : Interp D) (s : Letter) :
    MLe (restrictI C A s) (A s) := by
  intro i j
  unfold restrictI
  split_ifs
  · exact le_rfl
  · exact arc_zero_le _

/-- The restricted product is at most the original product (entrywise). -/
lemma ev_restrict_le (C : Finset (Fin D)) (A : Interp D) : ∀ w : Word,
    MLe (ev (restrictI C A) w) (ev A w)
  | [] => MLe.refl _
  | s :: w => by
    rw [ev_cons, ev_cons]
    exact mul_mono (restrictI_le C A s) (ev_restrict_le C A w)

/-- The end index of a finite entry of the restricted product lies in `C` (if the start index lies in `C`). -/
lemma ev_restrict_mem (C : Finset (Fin D)) (A : Interp D) : ∀ (w : Word) {m a : Fin D},
    ev (restrictI C A) w m a ≠ 0 → m ∈ C → a ∈ C
  | [], m, a, h, hm => by
    simp only [ev, List.map_nil, List.prod_nil] at h
    by_cases hma : m = a
    · exact hma ▸ hm
    · exact absurd (Matrix.one_apply_ne hma) h
  | s :: w, m, a, h, _ => by
    rw [ev_cons, mul_apply_ne_zero_iff] at h
    obtain ⟨n, hn, hna⟩ := h
    have hnC : n ∈ C := by
      unfold restrictI at hn
      split_ifs at hn with hc
      · exact hc.2
      · exact absurd rfl hn
    exact ev_restrict_mem C A w hna hnC

/-- A finite entry of a digit letter is an edge of `B₀ ∨ B₁`. -/
lemma reach_letter (A : Interp D) {s : Letter} (hs : s = Letter.f ∨ s = Letter.t) {a b : Fin D}
    (h : A s a b ≠ 0) : Reach (B0 A) (B1 A) a b := by
  apply Relation.ReflTransGen.single
  rcases hs with rfl | rfl
  · exact Or.inl h
  · exact Or.inr h

/-- A finite entry of a digit word gives reachability. -/
lemma reach_of_ev (A : Interp D) {w : Word} (hw : IsDigits w) {a b : Fin D} (h : ev A w a b ≠ 0) :
    Reach (B0 A) (B1 A) a b :=
  reach_of_mem (suppRel_ev_mem A w hw) a b h

/-- Reachability is realized by a finite entry of a digit word. -/
lemma exists_word_of_reach (A : Interp D) {a b : Fin D} (h : Reach (B0 A) (B1 A) a b) :
    ∃ w : Word, IsDigits w ∧ ev A w a b ≠ 0 := by
  induction h with
  | refl => exact ⟨[], fun s hs => by simp at hs, by simpa [ev] using one_apply_self_ne_zero a⟩
  | @tail b c _ hbc ih =>
    obtain ⟨w, hw, hab⟩ := ih
    have key : ∀ s : Letter, (s = Letter.f ∨ s = Letter.t) → A s b c ≠ 0 →
        ∃ w : Word, IsDigits w ∧ ev A w a c ≠ 0 := by
      intro s hs hsbc
      refine ⟨w ++ [s], isDigits_append hw (fun s' hs' => by
        rw [List.mem_singleton] at hs'; subst hs'; exact hs), ?_⟩
      rw [ev_append, mul_apply_ne_zero_iff]
      exact ⟨b, hab, by simpa [ev] using hsbc⟩
    rcases hbc with h0 | h1
    · exact key Letter.f (Or.inl rfl) h0
    · exact key Letter.t (Or.inr rfl) h1

/-- Convexity of a component: the points of a path between two points of `C` lie in `C`. -/
def PathConvex (A : Interp D) (C : Finset (Fin D)) : Prop :=
  ∀ x y z, x ∈ C → z ∈ C → Reach (B0 A) (B1 A) x y → Reach (B0 A) (B1 A) y z → y ∈ C

/-- A path reading a digit word between two points of a convex `C` stays inside `C`. -/
lemma ev_restrict_ne_zero (A : Interp D) {C : Finset (Fin D)} (hC : PathConvex A C) :
    ∀ (w : Word), IsDigits w → ∀ {m s : Fin D}, m ∈ C → s ∈ C → ev A w m s ≠ 0 →
      ev (restrictI C A) w m s ≠ 0
  | [], _, m, s, _, _, h => by simpa [ev] using h
  | a :: w, hw, m, s, hm, hs, h => by
    have ha : a = Letter.f ∨ a = Letter.t := hw a List.mem_cons_self
    have hw' : IsDigits w := fun s' hs' => hw s' (List.mem_cons_of_mem _ hs')
    rw [ev_cons, mul_apply_ne_zero_iff] at h
    obtain ⟨n, hmn, hns⟩ := h
    have hnC : n ∈ C := hC m n s hm hs (reach_letter A ha hmn) (reach_of_ev A hw' hns)
    rw [ev_cons, mul_apply_ne_zero_iff]
    refine ⟨n, ?_, ev_restrict_ne_zero A hC w hw' hnC hs hns⟩
    simp only [restrictI, hm, hnC, and_self, ↓reduceIte]
    exact hmn

section Classes

variable {A : Interp D} {E : BRel (Fin D)} (hE : E * E = E)

/-- The component `C(i)` is convex. -/
lemma pathConvex_comp (hEM : E ∈ Mon (B0 A) (B1 A)) (i : Cls E hE) {C : Finset (Fin D)}
    (hC : ∀ a, a ∈ C ↔ a ∈ comp (B0 A) (B1 A) hE i) : PathConvex A C := by
  intro x y z hx hz hxy hyz
  rw [hC] at hx hz ⊢
  obtain ⟨qx, hqx, hqxi, hxq, hqxx⟩ := hx
  obtain ⟨qz, hqz, hqzi, hzq, hqzz⟩ := hz
  have hzx : Reach (B0 A) (B1 A) qz qx :=
    reach_of_cls_eq hE hEM hqz hqx (hqzi.trans hqxi.symm)
  exact ⟨qx, hqx, hqxi, hyz.trans (hzq.trans hzx), hqxx.trans hxy⟩

/-- The component `C(i)` is strongly connected (`StrongConnIn`). -/
lemma strongConn_comp (hEM : E ∈ Mon (B0 A) (B1 A)) (i : Cls E hE) {C : Finset (Fin D)}
    (hC : ∀ a, a ∈ C ↔ a ∈ comp (B0 A) (B1 A) hE i) : StrongConnIn A C := by
  intro a ha b hb
  have ha' := (hC a).1 ha
  have hb' := (hC b).1 hb
  obtain ⟨qa, hqa, hqai, haq, hqaa⟩ := ha'
  obtain ⟨qb, hqb, hqbi, hbq, hqbb⟩ := hb'
  have hab : Reach (B0 A) (B1 A) a b :=
    haq.trans ((reach_of_cls_eq hE hEM hqa hqb (hqai.trans hqbi.symm)).trans hqbb)
  obtain ⟨w, hw, hne⟩ := exists_word_of_reach A hab
  exact ⟨w, hw, ev_restrict_ne_zero A (pathConvex_comp hE hEM i hC) w hw ha hb hne⟩

end Classes


/-! ### Lineages and restricted processes -/

/-- The conclusion of `HSP` holds for the word `w` for all `(C, S)` satisfying the premise (a good word). -/
def SPGood (A : Interp D) (ε' : ℝ) (w : Word) : Prop :=
  ∀ C S : Finset (Fin D), StrongConnIn A C → S ⊆ C → S.Nonempty → NeverDies A C S →
    ∀ b (v : ℕ), rowVal A C S w b = Arc.fin v → (rate A C - ε') * w.length ≤ v

/-- If the restricted process never dies from a set of starting indices, it never dies from its support after reading a word `c` either. -/
lemma neverDies_after {A : Interp D} {C S : Finset (Fin D)} (h : NeverDies A C S) (hS : S ⊆ C)
    (c : Word) (hc : IsDigits c) :
    NeverDies A C (C.filter (fun a => ∃ n ∈ S, ev (restrictI C A) c n a ≠ 0)) := by
  intro w hw
  obtain ⟨m, hm, s, hms⟩ := h (c ++ w) (isDigits_append hc hw)
  rw [ev_append, mul_apply_ne_zero_iff] at hms
  obtain ⟨a, hma, has⟩ := hms
  exact ⟨a, Finset.mem_filter.2 ⟨ev_restrict_mem C A c hma (hS hm), m, hm, hma⟩, s, has⟩

/-- Lower bound for one entry of the value vector. -/
lemma vecAfter_ge (v : Fin D → Arc) (A : Interp D) (w : Word) (a b : Fin D) :
    v a * ev A w a b ≤ vecAfter v A w b := by
  unfold vecAfter
  rw [Matrix.vecMul, dotProduct]
  exact Arc.le_sum_of_mem (s := Finset.univ) (fun a => v a * ev A w a b) (Finset.mem_univ a)

/-- Bound the value from below by the weight of one path. -/
lemma vec_step {u : Fin D → Arc} {A : Interp D} {P w : Word} {a b : Fin D} {x y : ℕ}
    {M : AMat D} (hM : MLe M (ev A w)) (ha : vecAfter u A P a = Arc.fin x)
    (hab : M a b = Arc.fin y) :
    ∃ v : ℕ, vecAfter u A (P ++ w) b = Arc.fin v ∧ x + y ≤ v := by
  apply arc_exists_of_fin_le
  rw [vecAfter_append]
  calc Arc.fin (x + y) = vecAfter u A P a * M a b := by rw [ha, hab, Arc.fin_mul_fin]
    _ ≤ vecAfter u A P a * ev A w a b := Arc.mul_le_mul_of_le le_rfl (hM a b)
    _ ≤ _ := vecAfter_ge _ A w a b

end Collatz.Arctic.Lower
