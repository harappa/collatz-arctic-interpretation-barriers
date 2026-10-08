/-
Counting in the proof of Lemma 6.6 of the paper. Probabilities are written as finite counts (fractions).

* Recounting through the bijection that splits digit words of length `m + n` into a front and a back part (`card_split`, `card_filter_take_eq`,
  `card_filter_drop_eq`).
* The number of words not containing `u*` (independence of disjoint blocks, `card_noInfix_le`), and long uniform words almost always contain `u*`
  (`noInfix_small`).
* From `HSP`: long uniform words are almost always good (`spgood_small`; a union bound over the finitely many `(C, S)` satisfying the premise).
* Total variation estimate (`tv_bad_le`): for a family whose law is within total variation distance `δ` of uniform, an event of uniform fraction at most `η` has fraction
  at most `η + δ` (no independence between the intervals is used).
* The uniform fraction of the bad event on one interval (the first `m` letters do not contain `u*`, or the rest is not a good word)
  (`interval_bad_le`, `interval_frac`).
-/
import CollatzProof.Arctic.LowerPath
import CollatzProof.Arctic.RateUpperBase

namespace Collatz.Arctic.Lower

open MinIdeal Matrix

variable {D : ℕ}

/-! ### Counting digit words -/

lemma mem_wordsOfLen_iff_digits {J : ℕ} {v : Word} : v ∈ wordsOfLen J ↔ v.length = J ∧ IsDigits v := by
  constructor
  · intro h
    refine ⟨length_of_mem_wordsOfLen h, ?_⟩
    unfold wordsOfLen at h
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp h
    intro s hs
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
    by_cases hg : g i <;> simp [hg]
  · rintro ⟨hl, hd⟩; exact mem_wordsOfLen_of hl hd

lemma card_wordsOfLen_eq (J : ℕ) : (wordsOfLen J).card = 2 ^ J := by
  unfold wordsOfLen
  rw [Finset.card_image_of_injective _ ?_]
  · simp
  · intro g₁ g₂ h
    have h' := List.ofFn_injective h
    funext i
    have hi := congrFun h' i
    by_cases a : g₁ i <;> by_cases b : g₂ i <;> simp_all

open Classical in
/-- Recounting through the bijection that splits words of length `m + n` into the first `m` letters and the rest. -/
lemma card_split (m n : ℕ) (P : Word → Word → Prop) :
    ((wordsOfLen (m + n)).filter (fun w => P (w.take m) (w.drop m))).card =
      ((wordsOfLen m ×ˢ wordsOfLen n).filter (fun p => P p.1 p.2)).card := by
  apply Finset.card_nbij' (fun w => (w.take m, w.drop m)) (fun p => p.1 ++ p.2)
  · intro w hw
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_wordsOfLen_iff_digits] at hw
    obtain ⟨⟨hl, hd⟩, hP⟩ := hw
    simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq, mem_wordsOfLen_iff_digits]
    refine ⟨⟨⟨by simp [hl], fun s hs => hd s (List.mem_of_mem_take hs)⟩,
      ⟨by simp [hl], fun s hs => hd s (List.mem_of_mem_drop hs)⟩⟩, hP⟩
  · rintro ⟨v₁, v₂⟩ hp
    simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq, mem_wordsOfLen_iff_digits] at hp
    obtain ⟨⟨⟨hl₁, hd₁⟩, hl₂, hd₂⟩, hP⟩ := hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_wordsOfLen_iff_digits]
    refine ⟨⟨by simp [hl₁, hl₂], fun s hs => ?_⟩, ?_⟩
    · rcases List.mem_append.mp hs with h | h
      · exact hd₁ s h
      · exact hd₂ s h
    · rw [List.take_left' hl₁, List.drop_left' hl₁]; exact hP
  · intro w _
    exact List.take_append_drop m w
  · rintro ⟨v₁, v₂⟩ hp
    simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq, mem_wordsOfLen_iff_digits] at hp
    obtain ⟨⟨⟨hl₁, -⟩, -⟩, -⟩ := hp
    simp [List.take_left' hl₁, List.drop_left' hl₁]

open Classical in
/-- The number of words satisfying an event on the first `m` letters. -/
lemma card_filter_take_eq (m n : ℕ) (P : Word → Prop) :
    ((wordsOfLen (m + n)).filter (fun w => P (w.take m))).card =
      ((wordsOfLen m).filter P).card * 2 ^ n := by
  rw [card_split m n (fun a _ => P a), ← card_wordsOfLen_eq n, ← Finset.card_product]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_product]
  tauto

open Classical in
/-- The number of words satisfying an event on the part after the first `m` letters. -/
lemma card_filter_drop_eq (m n : ℕ) (P : Word → Prop) :
    ((wordsOfLen (m + n)).filter (fun w => P (w.drop m))).card =
      2 ^ m * ((wordsOfLen n).filter P).card := by
  rw [card_split m n (fun _ b => P b), ← card_wordsOfLen_eq m, ← Finset.card_product]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_product]
  tauto


open Classical in
/-- The number of words not containing `u*`: among the words of length `k|u*| + r`, at most `(2^{|u*|} - 1)^k 2^r`
do not contain `u*` as a factor (independence of `k` disjoint blocks). -/
lemma card_noInfix_le (us : Word) (hu : IsDigits us) : ∀ k r : ℕ,
    ((wordsOfLen (k * us.length + r)).filter (fun w => ¬ us <:+: w)).card ≤
      (2 ^ us.length - 1) ^ k * 2 ^ r
  | 0, r => by
    simp only [Nat.zero_mul, Nat.zero_add, pow_zero, one_mul]
    exact (Finset.card_filter_le _ _).trans (card_wordsOfLen_eq r).le
  | k + 1, r => by
    have e : (k + 1) * us.length + r = us.length + (k * us.length + r) := by ring
    rw [e]
    calc ((wordsOfLen (us.length + (k * us.length + r))).filter (fun w => ¬ us <:+: w)).card
        ≤ ((wordsOfLen (us.length + (k * us.length + r))).filter
            (fun w => w.take us.length ≠ us ∧ ¬ us <:+: w.drop us.length)).card := by
          apply Finset.card_le_card
          intro w hw
          simp only [Finset.mem_filter] at hw ⊢
          refine ⟨hw.1, fun h => hw.2 ?_, fun h => hw.2 ?_⟩
          · rw [← List.take_append_drop us.length w, h]; exact (List.prefix_append _ _).isInfix
          · rw [← List.take_append_drop us.length w]
            exact h.trans (List.suffix_append _ _).isInfix
      _ = ((wordsOfLen us.length ×ˢ wordsOfLen (k * us.length + r)).filter
            (fun p => p.1 ≠ us ∧ ¬ us <:+: p.2)).card := by
          convert card_split us.length (k * us.length + r) (fun a b => a ≠ us ∧ ¬ us <:+: b)
            using 2 <;> (ext; simp)
      _ = ((wordsOfLen us.length).filter (fun v => v ≠ us)).card *
            ((wordsOfLen (k * us.length + r)).filter (fun v => ¬ us <:+: v)).card := by
          rw [← Finset.card_product]
          congr 1
          ext p
          simp only [Finset.mem_filter, Finset.mem_product]
          tauto
      _ ≤ (2 ^ us.length - 1) * ((2 ^ us.length - 1) ^ k * 2 ^ r) := by
          apply Nat.mul_le_mul
          · apply le_of_eq
            rw [Finset.filter_ne', Finset.card_erase_of_mem (mem_wordsOfLen_iff_digits.2 ⟨rfl, hu⟩),
              card_wordsOfLen_eq]
          · exact card_noInfix_le us hu k r
      _ = _ := by ring

open Classical in
/-- Long uniform words almost always contain `u*`. -/
lemma noInfix_small (us : Word) (hu : IsDigits us) {η : ℝ} (hη : 0 < η) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, (((wordsOfLen m).filter (fun w => ¬ us <:+: w)).card : ℝ) ≤
      η * 2 ^ m := by
  set ℓ := us.length with hℓ
  have h2 : (1 : ℝ) ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
  set ρ : ℝ := (2 ^ ℓ - 1) / 2 ^ ℓ with hρ
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one (by positivity)]; linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hη hρ1
  refine ⟨k * ℓ, fun m hm => ?_⟩
  have e : m = k * ℓ + (m - k * ℓ) := by omega
  have hc := card_noInfix_le us hu k (m - k * ℓ)
  rw [← e] at hc
  have hc' : (((wordsOfLen m).filter (fun w => ¬ us <:+: w)).card : ℝ) ≤
      ((2 : ℝ) ^ ℓ - 1) ^ k * 2 ^ (m - k * ℓ) := by
    have := (Nat.cast_le (α := ℝ)).mpr hc
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_pow]
      at this
    simpa using this
  have h2m : (2 : ℝ) ^ m = (2 ^ ℓ) ^ k * 2 ^ (m - k * ℓ) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    rw [Nat.mul_comm]; omega
  have hρ0 : 0 ≤ ρ := by rw [hρ]; apply div_nonneg <;> linarith
  calc _ ≤ ((2 : ℝ) ^ ℓ - 1) ^ k * 2 ^ (m - k * ℓ) := hc'
    _ = ρ ^ k * 2 ^ m := by
        rw [h2m, hρ, div_pow]
        field_simp
    _ ≤ η * 2 ^ m := by gcongr

/-- The premise of `HSP`. -/
def SPPrem {D : ℕ} (A : Interp D) (p : Finset (Fin D) × Finset (Fin D)) : Prop :=
  StrongConnIn A p.1 ∧ p.2 ⊆ p.1 ∧ p.2.Nonempty ∧ NeverDies A p.1 p.2

open Classical in
/-- From `HSP`: long uniform words are almost always good (a union bound over the finitely many `(C, S)` satisfying the premise). -/
lemma spgood_small (hSP : HSP) {D : ℕ} (A : Interp D) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ L₀ : ℕ, ∀ n ≥ L₀, (((wordsOfLen n).filter (fun w => ¬ SPGood A ε' w)).card : ℝ) ≤
      (Fintype.card (Finset (Fin D) × Finset (Fin D)) : ℝ) * ε' * 2 ^ n := by
  have hp : ∀ p : Finset (Fin D) × Finset (Fin D), SPPrem A p → ∃ L₀ : ℕ, ∀ L ≥ L₀,
      (1 - ε') * 2 ^ L ≤ ((((wordsOfLen L).filter (fun w => ∀ j (v : ℕ),
        rowVal A p.1 p.2 w j = Arc.fin v → (rate A p.1 - ε') * L ≤ v)).card : ℕ) : ℝ) :=
    fun p hp => hSP D A p.1 p.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 ε' hε'
  choose! Lf hLf using hp
  refine ⟨Finset.univ.sup Lf, fun n hn => ?_⟩
  set bad : Finset (Fin D) × Finset (Fin D) → Finset Word := fun p => (wordsOfLen n).filter
    (fun w => ¬ ∀ j (v : ℕ), rowVal A p.1 p.2 w j = Arc.fin v → (rate A p.1 - ε') * n ≤ v)
    with hbad_def
  have hbad : ∀ p, SPPrem A p → ((bad p).card : ℝ) ≤ ε' * 2 ^ n := by
    intro p hpp
    have h := hLf p hpp n ((Finset.le_sup (Finset.mem_univ p)).trans hn)
    have hsum := Finset.card_filter_add_card_filter_not (s := wordsOfLen n) (fun w => ∀ j (v : ℕ),
      rowVal A p.1 p.2 w j = Arc.fin v → (rate A p.1 - ε') * n ≤ v)
    rw [card_wordsOfLen_eq] at hsum
    have hsum' : ((((wordsOfLen n).filter (fun w => ∀ j (v : ℕ),
        rowVal A p.1 p.2 w j = Arc.fin v → (rate A p.1 - ε') * n ≤ v)).card : ℕ) : ℝ) +
        ((bad p).card : ℝ) = 2 ^ n := by
      rw [hbad_def]; exact_mod_cast hsum
    linarith
  have hsub : (wordsOfLen n).filter (fun w => ¬ SPGood A ε' w) ⊆
      (Finset.univ.filter (SPPrem A)).biUnion bad := by
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨hwn, hw⟩ := hw
    have hlen : w.length = n := length_of_mem_wordsOfLen hwn
    unfold SPGood at hw
    push Not at hw
    obtain ⟨C, S, h1, h2, h3, h4, b, v, hv, hlt⟩ := hw
    rw [Finset.mem_biUnion]
    refine ⟨(C, S), Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, h2, h3, h4⟩,
      Finset.mem_filter.2 ⟨hwn, ?_⟩⟩
    intro hall
    have := hall b v hv
    rw [hlen] at hlt
    linarith
  calc (((wordsOfLen n).filter (fun w => ¬ SPGood A ε' w)).card : ℝ)
      ≤ (((Finset.univ.filter (SPPrem A)).biUnion bad).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ p ∈ Finset.univ.filter (SPPrem A), ((bad p).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ p ∈ Finset.univ.filter (SPPrem A), ε' * 2 ^ n :=
        Finset.sum_le_sum (fun p hp => hbad p (Finset.mem_filter.1 hp).2)
    _ = ((Finset.univ.filter (SPPrem A)).card : ℝ) * (ε' * 2 ^ n) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card (Finset (Fin D) × Finset (Fin D)) : ℝ) * (ε' * 2 ^ n) := by
        gcongr
        exact_mod_cast Finset.card_le_univ _
    _ = _ := by ring

/-- **Total variation estimate**: if the law of `B` (under the uniform weight on `X`) is within total variation distance `δ` of uniform and the uniform
fraction of bad words is at most `η`, then the fraction of `x` with `B x` bad is at most `η + δ`. -/
lemma tv_bad_le {ι : Type*} (X : Finset ι) (B : ι → Word) (L : ℕ)
    (hB : ∀ x ∈ X, B x ∈ wordsOfLen L) (Bad : Word → Prop) [DecidablePred Bad] {η δ : ℝ}
    (hη : (((wordsOfLen L).filter Bad).card : ℝ) ≤ η * 2 ^ L)
    (hTV : ∑ v ∈ wordsOfLen L,
      |(((X.filter (fun x => B x = v)).card : ℝ) / X.card) - 1 / 2 ^ L| ≤ 2 * δ) :
    ((X.filter (fun x => Bad (B x))).card : ℝ) ≤ (η + δ) * X.card := by
  rcases X.eq_empty_or_nonempty with hX | hX
  · subst hX; simp
  have hn : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  set W := wordsOfLen L with hWdef
  set c : Word → ℝ := fun v => ((X.filter (fun x => B x = v)).card : ℝ) with hc
  set q : ℝ := 1 / 2 ^ L with hq
  set d : Word → ℝ := fun v => c v / X.card - q with hd
  have htot : ∑ v ∈ W, c v = X.card := by
    have := Finset.card_eq_sum_card_fiberwise (f := B) (s := X) (t := W) hB
    show ∑ v ∈ W, ((X.filter (fun x => B x = v)).card : ℝ) = X.card
    exact_mod_cast this.symm
  have hW : (W.card : ℝ) * q = 1 := by
    rw [hWdef, card_wordsOfLen_eq, hq]; push_cast; field_simp
  have hbad : ((X.filter (fun x => Bad (B x))).card : ℝ) = ∑ v ∈ W.filter Bad, c v := by
    have := Finset.card_eq_sum_card_fiberwise (f := B) (s := X.filter (fun x => Bad (B x)))
      (t := W.filter Bad) (fun x hx => by
        rw [Finset.mem_coe, Finset.mem_filter] at hx ⊢
        exact ⟨hB x hx.1, hx.2⟩)
    rw [this]
    push_cast
    refine Finset.sum_congr rfl (fun v hv => ?_)
    rw [hc]
    congr 2
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hx, -⟩, hxv⟩; exact ⟨hx, hxv⟩
    · rintro ⟨hx, hxv⟩; exact ⟨⟨hx, hxv ▸ (Finset.mem_filter.1 hv).2⟩, hxv⟩
  have hzero : ∑ v ∈ W, d v = 0 := by
    rw [hd, Finset.sum_sub_distrib, ← Finset.sum_div, htot, Finset.sum_const, nsmul_eq_mul, hW,
      div_self hn.ne']
    ring
  have hsplit := Finset.sum_filter_add_sum_filter_not W Bad d
  have habs := Finset.sum_filter_add_sum_filter_not W Bad (fun v => |d v|)
  have h1 : ∑ v ∈ W.filter Bad, d v ≤ ∑ v ∈ W.filter Bad, |d v| :=
    Finset.sum_le_sum (fun v _ => le_abs_self _)
  have h2 : -∑ v ∈ W.filter (fun v => ¬ Bad v), d v ≤
      ∑ v ∈ W.filter (fun v => ¬ Bad v), |d v| := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun v _ => neg_le_abs _)
  have hTV' : ∑ v ∈ W, |d v| ≤ 2 * δ := hTV
  have hdBad : ∑ v ∈ W.filter Bad, d v ≤ δ := by linarith
  have hcBad : ∑ v ∈ W.filter Bad, c v =
      X.card * (∑ v ∈ W.filter Bad, d v + (W.filter Bad).card * q) := by
    rw [hd, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_div]
    field_simp
    ring
  have hq' : ((W.filter Bad).card : ℝ) * q ≤ η := by
    rw [hq]
    have : (0 : ℝ) < 2 ^ L := by positivity
    rw [mul_one_div, div_le_iff₀ this]
    exact hη
  rw [hbad, hcBad]
  nlinarith


open Classical in
/-- The uniform fraction of the complement of the good event on an interval (the first `m` letters contain `u*` and the rest is a good word). -/
lemma interval_bad_le {D : ℕ} (A : Interp D) (us : Word) {ε' η₁ η₂ : ℝ} (m n : ℕ)
    (h1 : (((wordsOfLen m).filter (fun w => ¬ us <:+: w)).card : ℝ) ≤ η₁ * 2 ^ m)
    (h2 : (((wordsOfLen n).filter (fun w => ¬ SPGood A ε' w)).card : ℝ) ≤ η₂ * 2 ^ n) :
    (((wordsOfLen (m + n)).filter
      (fun w => ¬ (us <:+: w.take m ∧ SPGood A ε' (w.drop m)))).card : ℝ) ≤
      (η₁ + η₂) * 2 ^ (m + n) := by
  have hsub : (wordsOfLen (m + n)).filter
      (fun w => ¬ (us <:+: w.take m ∧ SPGood A ε' (w.drop m))) ⊆
      (wordsOfLen (m + n)).filter (fun w => ¬ us <:+: w.take m) ∪
        (wordsOfLen (m + n)).filter (fun w => ¬ SPGood A ε' (w.drop m)) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases h : us <:+: w.take m
    · exact Or.inr ⟨hw.1, fun h' => hw.2 ⟨h, h'⟩⟩
    · exact Or.inl ⟨hw.1, h⟩
  have c1 : ((wordsOfLen (m + n)).filter (fun w => ¬ us <:+: w.take m)).card =
      ((wordsOfLen m).filter (fun w => ¬ us <:+: w)).card * 2 ^ n := by
    convert card_filter_take_eq m n (fun w => ¬ us <:+: w)
  have c2 : ((wordsOfLen (m + n)).filter (fun w => ¬ SPGood A ε' (w.drop m))).card =
      2 ^ m * ((wordsOfLen n).filter (fun w => ¬ SPGood A ε' w)).card := by
    convert card_filter_drop_eq m n (fun w => ¬ SPGood A ε' w)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [c1, c2] at hc
  have hc' : (((wordsOfLen (m + n)).filter
      (fun w => ¬ (us <:+: w.take m ∧ SPGood A ε' (w.drop m)))).card : ℝ) ≤
      (((wordsOfLen m).filter (fun w => ¬ us <:+: w)).card : ℝ) * 2 ^ n +
        2 ^ m * (((wordsOfLen n).filter (fun w => ¬ SPGood A ε' w)).card : ℝ) := by
    exact_mod_cast hc
  rw [pow_add]
  calc _ ≤ _ := hc'
    _ ≤ (η₁ * 2 ^ m) * 2 ^ n + 2 ^ m * (η₂ * 2 ^ n) := by gcongr
    _ = _ := by ring

open Classical in
/-- One interval: if `L ≥ κ m₀ + 2 L_S`, the uniform fraction of the bad event with the split `m := L / κ` is at most `η + NP ε'`. -/
lemma interval_frac {D : ℕ} (A : Interp D) (us : Word) {ε' η c : ℝ} {m₀ LS κ : ℕ} (hκ2 : 2 ≤ κ)
    (hm₀ : ∀ m ≥ m₀, (((wordsOfLen m).filter (fun w => ¬ us <:+: w)).card : ℝ) ≤ η * 2 ^ m)
    (hLS : ∀ n ≥ LS, (((wordsOfLen n).filter (fun w => ¬ SPGood A ε' w)).card : ℝ) ≤
      c * 2 ^ n)
    (L : ℕ) (hL : κ * m₀ + 2 * LS ≤ L) :
    (((wordsOfLen L).filter (fun w => ¬ (us <:+: w.take (L / κ) ∧
        SPGood A ε' (w.drop (L / κ))))).card : ℝ) ≤ (η + c) * 2 ^ L := by
  have hmL : L / κ ≤ L := Nat.div_le_self L κ
  have hm : m₀ ≤ L / κ := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    nlinarith
  have hhalf : L / κ ≤ L / 2 := Nat.div_le_div_left hκ2 (by norm_num)
  have hn : LS ≤ L - L / κ := by omega
  have h := interval_bad_le A us (L / κ) (L - L / κ) (hm₀ _ hm) (hLS _ hn)
  have he : L / κ + (L - L / κ) = L := Nat.add_sub_cancel' hmL
  rw [he] at h
  exact h


end Collatz.Arctic.Lower
