/-
The Terras correspondence for $H$ at the block level, and the interface statements. Of the statements of the frozen
`HModel/Defs.lean`, this file proves
the following three (the swap `SpecHSwap` is in `Swap.lean`).

* `specHModel : SpecHModel`: the fields of the model (`R_lt`, `C_lt`, `R_prefix`, `iter`, `orbit_dom`, `f_pos`).
* `specHClass : SpecHClass`: the residue classes along orbits ($\equiv 0 \pmod 4$ if the `i`-th letter is $\mathsf a$, $\equiv 7 \pmod 8$ if it is $\mathsf b$).
* `specHBoundary : SpecHBoundary`: the form of block boundary points (the form of `TModel.terras_prefix`).

**Block level**: `wm_lettersOf` (the number of bits $m = $ `(parityOf β).length` $= 8\#X + 11\#Y$), `wa_lettersOf`
(the exponent of 3, $a = $ `terrasA (parityOf β)` $= 5\#X + 7\#Y$). The shape is that of the model of $T$; only the number of steps `hSteps β`
(3 or 4 per block) differs. `orbit_dom` follows since every block ends with $\mathsf b$, so the remaining word contains $\mathsf b$
(`false_mem_drop_lettersOf`) and has at least 3 bits (`three_le_wm_drop`), hence the orbit points are
at least $2^3 t \ge 8$, together with the residue classes along the orbit (`h_class`). For the boundary points, the word is split into
the letter words of $\beta_{<i}$ and $\beta_{\ge i}$ and `h_prefix` is applied ($m - L_i = $ `(parityOf (β.drop i)).length`).

**Adapted from**: `TModel.lean` (`terras_prefix`, `terras_orbit_two_le`) and the fields of `tModel` in `Gen/Model.lean`.
Correspondence with the paper: the model of $H$ in Proposition 7.2 ($X = \mathsf{abb}$, $Y = \mathsf{abbb}$), the point family of Section 6.1, the domain $x \ge 8$ (Section 2.3).
-/
import CollatzProof.Arctic.HModel.Terras

namespace Collatz.Arctic.HModel

open Collatz.Arctic

/-! ## Block level -/

lemma lettersOf_nil : lettersOf [] = [] := rfl

lemma lettersOf_cons (x : Bool) (β : List Bool) :
    lettersOf (x :: β) = (if x then [true, false, false] else [true, false, false, false]) ++ lettersOf β := by
  simp [lettersOf]

lemma lettersOf_append (β₁ β₂ : List Bool) : lettersOf (β₁ ++ β₂) = lettersOf β₁ ++ lettersOf β₂ := by
  simp [lettersOf, List.flatMap_append]

lemma parityOf_cons (x : Bool) (β : List Bool) :
    parityOf (x :: β) = (if x then blkX else blkY) ++ parityOf β := by
  simp [parityOf]

lemma parityOf_append (β₁ β₂ : List Bool) : parityOf (β₁ ++ β₂) = parityOf β₁ ++ parityOf β₂ := by
  simp [parityOf, List.flatMap_append]

lemma terrasA_blkX : terrasA blkX = 5 := by rw [terrasA_eq]; decide
lemma terrasA_blkY : terrasA blkY = 7 := by rw [terrasA_eq]; decide

/-- The number of bits of a block sequence has the same form as for $T$: $m = $ `(parityOf β).length`. -/
theorem wm_lettersOf (β : List Bool) : wm (lettersOf β) = (parityOf β).length := by
  induction β with
  | nil => rfl
  | cons x β ih =>
    rw [lettersOf_cons, parityOf_cons, wm_append, ih, List.length_append]
    cases x <;> simp [wm_eq, lbits, blkX, blkY]

/-- The exponent of 3 of a block sequence has the same form as for $T$: $a = $ `terrasA (parityOf β)`. -/
theorem wa_lettersOf (β : List Bool) : wa (lettersOf β) = terrasA (parityOf β) := by
  induction β with
  | nil => rfl
  | cons x β ih =>
    rw [lettersOf_cons, parityOf_cons, wa_append, ih, terrasA_append]
    cases x <;> simp [wa_eq, lthree, terrasA_blkX, terrasA_blkY]

lemma hR_eq (β : List Bool) : hR β = wr (lettersOf β) := rfl
lemma hC_eq (β : List Bool) : hC β = wc (lettersOf β) := rfl

/-- In terms of the state: the number of bits. -/
lemma hState_fst_lettersOf (β : List Bool) : (hState (lettersOf β)).1 = (parityOf β).length :=
  wm_lettersOf β

/-- In terms of the state: the exponent of 3. -/
lemma hState_a_lettersOf (β : List Bool) : (hState (lettersOf β)).2.2.2 = terrasA (parityOf β) :=
  wa_lettersOf β

/-- The residue of concatenated block sequences (the form of `TModel.terrasR_append`). -/
theorem hR_append (β₁ β₂ : List Bool) :
    ∃ r' < 2 ^ (parityOf β₂).length, hR (β₁ ++ β₂) = hR β₁ + 2 ^ (parityOf β₁).length * r' := by
  rw [hR_eq, hR_eq, lettersOf_append, ← wm_lettersOf, ← wm_lettersOf]
  exact wr_append _ _

/-- The number of steps is additive under concatenation. -/
lemma hSteps_append (β₁ β₂ : List Bool) : hSteps (β₁ ++ β₂) = hSteps β₁ + hSteps β₂ := by
  simp [hSteps, lettersOf_append]

/-- Since every block ends with $\mathsf b$, the letter word contains $\mathsf b$ at or after every position. -/
theorem false_mem_drop_lettersOf (β : List Bool) :
    ∀ i < (lettersOf β).length, false ∈ (lettersOf β).drop i := by
  induction β with
  | nil => intro i hi; simp [lettersOf_nil] at hi
  | cons x β ih =>
    intro i hi
    rw [lettersOf_cons] at hi ⊢
    rw [List.drop_append, List.mem_append]
    by_cases hb : i < (if x then [true, false, false] else [true, false, false, false]).length
    · left
      cases x
      · simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil] at hb ⊢
        interval_cases i <;> simp
      · simp only [↓reduceIte, List.length_cons, List.length_nil] at hb ⊢
        interval_cases i <;> simp
    · right
      rw [List.length_append] at hi
      exact ih _ (by omega)

/-- The remaining word has at least 3 bits. -/
theorem three_le_wm_drop (β : List Bool) (i : ℕ) (hi : i < (lettersOf β).length) :
    3 ≤ wm ((lettersOf β).drop i) := by
  rw [wm_eq]
  have hmem : lbits false ∈ ((lettersOf β).drop i).map lbits :=
    List.mem_map_of_mem (false_mem_drop_lettersOf β i hi)
  exact List.le_sum_of_mem hmem

/-! ## Interface statements -/

/-- **Interface statement**: the fields of the model. -/
theorem specHModel : SpecHModel where
  R_lt β := by rw [hR_eq, ← wm_lettersOf]; exact wr_lt _
  C_lt β := by rw [hC_eq, ← wa_lettersOf]; exact wc_lt _
  R_prefix β₁ β₂ := by
    rw [hR_eq, hR_eq, lettersOf_append, ← wm_lettersOf]
    obtain ⟨r', _, hR⟩ := wr_append (lettersOf β₁) (lettersOf β₂)
    rw [hR, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wr_lt _)]
  iter β t := by
    rw [hR_eq, hC_eq, ← wm_lettersOf, ← wa_lettersOf]
    exact h_iter _ t
  orbit_dom β t ht i hi := by
    rw [hR_eq, ← wm_lettersOf]
    have hi' : i < (lettersOf β).length := hi
    have hcl := h_class (lettersOf β) t i hi'
    have hge := h_orbit_ge (lettersOf β) t i hi'.le
    have h3 := three_le_wm_drop β i hi'
    have h8 : 8 ≤ 2 ^ wm ((lettersOf β).drop i) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) h3
    have h8' : 8 ≤ 2 ^ wm ((lettersOf β).drop i) * t := le_trans h8 (Nat.le_mul_of_pos_right _ ht)
    refine ⟨le_trans h8' hge, ?_⟩
    split_ifs at hcl
    · exact Or.inl hcl
    · exact Or.inr hcl
  f_pos n hn := by
    obtain ⟨h8, _⟩ := hn
    unfold Hmap; split_ifs <;> omega

/-- **Interface statement**: the residue classes along orbits. -/
theorem specHClass : SpecHClass := by
  intro β t i hi
  rw [hR_eq, ← wm_lettersOf]
  exact h_class (lettersOf β) t i hi

/-- **Interface statement**: the form of block boundary points (the form of `terras_prefix`). -/
theorem specHBoundary : SpecHBoundary := by
  intro β t i _
  obtain ⟨r', hr', _, hit⟩ := h_prefix (lettersOf (β.take i)) (lettersOf (β.drop i))
  have hL : (parityOf β).length - blockEnd β i = (parityOf (β.drop i)).length := by
    have hs : parityOf β = parityOf (β.take i) ++ parityOf (β.drop i) := by
      rw [← parityOf_append, List.take_append_drop]
    unfold blockEnd
    rw [hs, List.length_append]
    omega
  rw [hL]
  have h := hit t
  rw [← lettersOf_append, List.take_append_drop] at h
  simp only [wm_lettersOf, wa_lettersOf] at h
  rw [wm_lettersOf] at hr'
  exact ⟨r', hr', h⟩

end Collatz.Arctic.HModel
