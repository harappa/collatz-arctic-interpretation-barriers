/-
Common lemmas for the assembly (Theorem 6.8): supports of products, types of words and `typ` of `TransportStay.lean`, concatenation and supports of value vectors.
-/
import CollatzProof.Arctic.Config
import CollatzProof.Arctic.Bridge
import CollatzProof.Arctic.AutoStatement

namespace Collatz.Arctic

open MinIdeal Matrix

variable {D : ℕ}

namespace Arc

lemma ne_zero_iff_val (a : Arc) : a ≠ 0 ↔ val a ≠ ⊥ :=
  ⟨fun h h' => h (ext (by simpa using h')), fun h h' => h (by rw [h']; rfl)⟩

lemma mul_ne_zero_iff (a b : Arc) : a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := by
  rw [ne_zero_iff_val, ne_zero_iff_val, ne_zero_iff_val, val_mul]
  constructor
  · intro h
    exact ⟨fun ha => h (by rw [ha]; simp), fun hb => h (by rw [hb]; simp)⟩
  · rintro ⟨ha, hb⟩ hab
    rcases WithBot.add_eq_bot.mp hab with h | h
    · exact ha h
    · exact hb h

lemma sum_ne_zero_iff {ι : Type*} (s : Finset ι) (f : ι → Arc) :
    (∑ i ∈ s, f i) ≠ 0 ↔ ∃ i ∈ s, f i ≠ 0 := by
  rw [ne_zero_iff_val, val_sum]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    apply h
    rw [Finset.sup_eq_bot_iff]
    intro i hi
    have := hc i hi
    rw [this]; rfl
  · rintro ⟨i, hi, hfi⟩ hsup
    rw [Finset.sup_eq_bot_iff] at hsup
    exact (ne_zero_iff_val _).mp hfi (hsup i hi)

end Arc

/-- Supports of products: `supp(M N) = supp M · supp N` (there is no cancellation in arctic arithmetic). -/
theorem suppRel_mul (M N : AMat D) : suppRel (M * N) = suppRel M * suppRel N := by
  funext i j
  apply propext
  show (M * N) i j ≠ 0 ↔ ∃ k, M i k ≠ 0 ∧ N k j ≠ 0
  rw [Matrix.mul_apply, Arc.sum_ne_zero_iff]
  simp only [Finset.mem_univ, true_and, Arc.mul_ne_zero_iff]

theorem suppRel_one : suppRel (1 : AMat D) = (1 : BRel (Fin D)) := by
  funext i j
  apply propext
  show (1 : AMat D) i j ≠ 0 ↔ i = j
  rw [Matrix.one_apply]
  by_cases h : i = j
  · simp only [h, ↓reduceIte, iff_true]
    intro h1
    have := congrArg Arc.val h1
    simp at this
  · simp [h]

theorem suppRel_ev_append (A : Interp D) (w₁ w₂ : Word) :
    suppRel (ev A (w₁ ++ w₂)) = suppRel (ev A w₁) * suppRel (ev A w₂) := by
  rw [ev_append, suppRel_mul]

/-- The type of a digit word is `typ` of `TransportStay.lean` (`f ↦ B0`, `t ↦ B1`). -/
theorem suppRel_ev_digits (A : Interp D) :
    ∀ w : Word, IsDigits w → suppRel (ev A w) = typ (B0 A) (B1 A) (w.map toBool)
  | [], _ => by simp [ev, typ, suppRel_one]
  | s :: w, hw => by
    have hs := hw s List.mem_cons_self
    have hw' : IsDigits w := fun s' hs' => hw s' (List.mem_cons_of_mem _ hs')
    rw [ev_cons, suppRel_mul, suppRel_ev_digits A w hw']
    have : typ (B0 A) (B1 A) ((s :: w).map toBool) =
        letter (B0 A) (B1 A) (toBool s) * typ (B0 A) (B1 A) (w.map toBool) := by simp [typ]
    rw [this]
    congr 1
    rcases hs with rfl | rfl <;> simp [letter, toBool, B0, B1]

/-- The type of a digit word lies in the monoid `Mon (B0 A) (B1 A)`. -/
theorem suppRel_ev_mem (A : Interp D) (w : Word) (hw : IsDigits w) :
    suppRel (ev A w) ∈ Mon (B0 A) (B1 A) := by
  rw [suppRel_ev_digits A w hw]; exact typ_mem _

/-- Concatenation of value vectors. -/
theorem vecAfter_append (u : Fin D → Arc) (A : Interp D) (w₁ w₂ : Word) :
    vecAfter u A (w₁ ++ w₂) = vecAfter (vecAfter u A w₁) A w₂ := by
  simp [vecAfter, ev_append, Matrix.vecMul_vecMul]

/-- The support of a value vector is the initial support acted on by the type of the word. -/
theorem suppV_vecAfter (u : Fin D → Arc) (A : Interp D) (w : Word) :
    suppV (vecAfter u A w) = act (suppV u) (suppRel (ev A w)) := by
  ext j
  show (u ᵥ* ev A w) j ≠ 0 ↔ ∃ i ∈ suppV u, ev A w i j ≠ 0
  rw [Matrix.vecMul, dotProduct, Arc.sum_ne_zero_iff]
  simp only [Finset.mem_univ, true_and, Arc.mul_ne_zero_iff]
  rfl

/-- `autoVal` is the inner product of the value vector with `c`. -/
theorem autoVal_eq (u : Fin D → Arc) (A : Interp D) (c : Fin D → Arc) (n : ℕ) :
    autoVal u A c n = vecAfter u A (binTail n) ⬝ᵥ c := by
  simp [autoVal, vecAfter, Matrix.dotProduct_mulVec]

end Collatz.Arctic
