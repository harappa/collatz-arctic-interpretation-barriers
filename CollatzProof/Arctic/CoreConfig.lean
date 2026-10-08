/-
Parts of the assembly of Theorem 6.8 of the paper: counting digit words, and configurations.
* `bitsMSB m` is a bijection from `range (2^m)` to `wordsOfLen m` (`card_filter_bitsMSB`). `wordsOfLen m` is in
  one-to-one correspondence with `Fin m → Bool` (`card_filter_wordsOfLen_toBool`). This connects the uniform count of the free bits with
  `Dfa.count_words` (a count over `Fin n → Bool`) for the DFA.
* The configuration `cfgOf` after reading the word `y₁` from the state `X` (the upper set at the end of the occurrence of `u*`; this is the
  configuration `I(X)` of the proof of Theorem 6.8, determined by the state of the support DFA).
-/
import CollatzProof.Arctic.SupportDfa
import CollatzProof.Arctic.TModel
import CollatzProof.Arctic.RateUpperBase

namespace Collatz.Arctic

open MinIdeal Classical

/-! ## Counting digit words -/

/-- Value of a binary word (most significant digit first). -/
def valMSB : Word → ℕ
  | [] => 0
  | s :: w => (if s = Letter.t then 1 else 0) * 2 ^ w.length + valMSB w

theorem valMSB_bitsMSB : ∀ (m r : ℕ), r < 2 ^ m → valMSB (bitsMSB m r) = r
  | 0, r, hr => by simp at hr; subst hr; rfl
  | m + 1, r, hr => by
    simp only [bitsMSB, valMSB, bitsMSB_length]
    rw [valMSB_bitsMSB m (r % 2 ^ m) (Nat.mod_lt _ (by positivity))]
    have hq : r / 2 ^ m < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [pow_succ] at hr; omega
    have hdm := Nat.mod_add_div r (2 ^ m)
    have h01 : r / 2 ^ m = 0 ∨ r / 2 ^ m = 1 :=
      Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hq)
    rcases h01 with h0 | h1
    · have hb : bitL (r / 2 ^ m % 2) = Letter.f := by rw [h0]; rfl
      rw [h0, mul_zero, add_zero] at hdm
      simp only [hb, reduceCtorEq, ↓reduceIte, zero_mul, zero_add]; exact hdm
    · have hb : bitL (r / 2 ^ m % 2) = Letter.t := by rw [h1]; rfl
      rw [h1, mul_one] at hdm
      simp only [hb, ↓reduceIte, one_mul]
      omega

theorem bitsMSB_isDigits : ∀ (m r : ℕ), IsDigits (bitsMSB m r)
  | 0, _ => by intro s hs; simp [bitsMSB] at hs
  | m + 1, r => by
    intro s hs
    simp only [bitsMSB, List.mem_cons] at hs
    rcases hs with rfl | hs
    · unfold bitL; split_ifs <;> simp
    · exact bitsMSB_isDigits m _ s hs

theorem bitsMSB_mem_wordsOfLen (m r : ℕ) : bitsMSB m r ∈ wordsOfLen m :=
  mem_wordsOfLen_of (bitsMSB_length m r) (bitsMSB_isDigits m r)

theorem bitsMSB_injOn (m : ℕ) : Set.InjOn (bitsMSB m) (Finset.range (2 ^ m) : Set ℕ) := by
  intro r hr r' hr' h
  simp only [Finset.coe_range, Set.mem_Iio] at hr hr'
  rw [← valMSB_bitsMSB m r hr, ← valMSB_bitsMSB m r' hr', h]

theorem card_wordsOfLen (m : ℕ) : (wordsOfLen m).card = 2 ^ m := by
  unfold wordsOfLen
  rw [Finset.card_image_of_injective]
  · simp
  · intro g g' h
    funext i
    have := congrArg (fun l => l[i.val]?) h
    simp only [List.getElem?_ofFn] at this
    by_cases hg : g i <;> by_cases hg' : g' i <;> simp_all

theorem image_bitsMSB (m : ℕ) : (Finset.range (2 ^ m)).image (bitsMSB m) = wordsOfLen m := by
  apply Finset.eq_of_subset_of_card_le
  · intro w hw
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hw
    exact bitsMSB_mem_wordsOfLen m r
  · rw [card_wordsOfLen, Finset.card_image_of_injOn (bitsMSB_injOn m), Finset.card_range]

/-- The uniform count of the free bits is a count of digit words of length `m`. -/
theorem card_filter_bitsMSB (m : ℕ) (P : Word → Prop) [DecidablePred P] :
    ((Finset.range (2 ^ m)).filter (fun u => P (bitsMSB m u))).card = ((wordsOfLen m).filter P).card := by
  rw [← image_bitsMSB, Finset.filter_image, Finset.card_image_of_injOn]
  exact (bitsMSB_injOn m).mono (by intro x hx; exact Finset.mem_coe.mpr (Finset.mem_of_mem_filter _ hx))

/-- The count of digit words of length `m` is a count over `Fin m → Bool` (the DFA reads them through `toBool`). -/
theorem card_filter_wordsOfLen_toBool (m : ℕ) (Q : List Bool → Prop) [DecidablePred Q] :
    ((wordsOfLen m).filter (fun w => Q (w.map toBool))).card =
      ((Finset.univ : Finset (Fin m → Bool)).filter (fun g => Q (List.ofFn g))).card := by
  unfold wordsOfLen
  rw [Finset.filter_image, Finset.card_image_of_injOn]
  · congr 1
    apply Finset.filter_congr
    intro g _
    have : (List.ofFn (fun i => if g i then Letter.t else Letter.f)).map toBool = List.ofFn g := by
      rw [List.map_ofFn]
      congr 1
      funext i
      by_cases h : g i <;> simp [h, toBool]
    rw [this]
  · intro g _ g' _ h
    funext i
    have := congrArg (fun l => l[i.val]?) h
    simp only [List.getElem?_ofFn] at this
    by_cases hg : g i <;> by_cases hg' : g' i <;> simp_all

/-! ## Configurations -/

variable {D : ℕ}

/-- The configuration: read the word `y₁` from the state `X`; the upper set at the end of the following occurrence of `u*` (of type `E`). -/
def cfgOf (A : Interp D) {E : BRel (Fin D)} (hE : E * E = E) (y₁ : Word) (X : Finset (Fin D)) :
    Set (Cls E hE) :=
  hitSet hE (act ↑X (suppRel (ev A y₁)))

/-- The classes hit after reading the word `pre ++ y₁` form the configuration of the state of the support DFA after `pre`. -/
theorem hitSet_vecAfter_eq_cfgOf (u : Fin D → Arc) (A : Interp D) {E : BRel (Fin D)} (hE : E * E = E)
    (pre y₁ : Word) :
    hitSet hE (suppV (vecAfter u A (pre ++ y₁))) = cfgOf A hE y₁ (suppF (vecAfter u A pre)) := by
  unfold cfgOf
  rw [vecAfter_append, suppV_vecAfter, coe_suppF]

end Collatz.Arctic
