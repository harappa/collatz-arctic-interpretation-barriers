/-
# Geometry of the tails of detours (Lemma 12.25 and Proposition 12.26 of the paper)

Counting is by group indices, and detours lead to `RunMiss`, including the positions below group 0. Detours of long
range require a long window without `u♯` (`DecompData.g_free`). That window is split into the zones of the word of the starting point (top, free bits, `ρ`, Terras
part, shared part); after removing the zones of constant length, a long window without `u♯` remains in the free bits or in the Terras part
(`tail_split`). A window in the Terras part covers the cut words of consecutive groups entirely and causes `RunMiss` (`runMiss_of_run`,
`card_run_le_runMiss`).

* `freeW_sub`, `tail_split`: splitting a window into zones (after removing the total length `C₀` of the zones, one of the two parts has length at least `L`).
* `card_exists_le`: the number of positions `p` such that some window begins within `r` from `p` is at most `(r+1) |Y|`.
* `tail_sum_le`: the sum over positions of the weights of the detours of the item `i` with range in `(J, N]` is at most the sum over ranges of `c_P (r+1)^{d_P+1}` times the numbers of windows
  without `u♯` in the two zones (for `r` the window length is `Lr r := (ℓ₀(r) - C₀)/2`).
* **Window in the Terras part ⇒ `RunMiss`**: `blockEnd_sub_le` (a block has at most 11 bits), `not_gHit_of_cover` (a window that covers the cut word of a group
  does not contain `u♯`, so the group misses), `runMiss_of_group`, `runMiss_of_partial` (windows at the positions of a group, and at the positions of the incomplete top group),
  `card_run_le_runMiss` (the number of windows is at most `22g Σ_{i<G} [RunMiss i K K]`, `L ≥ 11g(K+2)`, `K ≥ 1`).
* The count on the side of the free bits, `card_free_run_le`.
-/
import CollatzProof.Arctic.Nat.W3hEval
import CollatzProof.Arctic.Nat.W3GapTail

namespace Collatz.Arctic.NatQ5.W3h

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W3c
open Collatz.Arctic.MinIdeal (BRel)

set_option linter.unusedSectionVars false

/-! ## §1 Splitting a window into zones -/

theorem freeW_sub {us l : List (Fin 2)} {x ℓ x' ℓ' : ℕ} (h : FreeW us x ℓ l) (h1 : x ≤ x')
    (h2 : x' + ℓ' ≤ x + ℓ) : FreeW us x' ℓ' l := fun hc => h (hc.trans (infix_drop_take l h1 h2))

theorem drop_take_append_left {α : Type*} {A B : List α} {y L : ℕ} (h : y + L ≤ A.length) :
    ((A ++ B).drop y).take L = (A.drop y).take L := by
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

/-- In the word `X ++ R`, the segment of length `L` at position `|X| + y` (`y + L ≤ |A|`, `R = A ++ B`) is the segment of length `L` of `A` at position `y`. -/
theorem seg_shift {α : Type*} (X A B : List α) {y L : ℕ} (h : y + L ≤ A.length) :
    ((X ++ A ++ B).drop (X.length + y)).take L = (A.drop y).take L := by
  rw [List.append_assoc, ← List.drop_drop, List.drop_left' rfl]
  exact drop_take_append_left h

/-- **Splitting a window into zones**: a window `[x, x+ℓ)` without `u♯`, after removing the zones `X₀`, `X₁`, `X₂` of constant length, has a part of length at least `L` without `u♯`
inside `F` or `T` (`2L + |X₀| + |X₁| + |X₂| ≤ ℓ`). -/
theorem tail_split (us X₀ Fw X₁ Tw X₂ : List (Fin 2)) (L : ℕ) (hL : 1 ≤ L) {x ℓ : ℕ}
    (hx : x + ℓ ≤ X₀.length + Fw.length + X₁.length + Tw.length + X₂.length)
    (hℓ : 2 * L + X₀.length + X₁.length + X₂.length ≤ ℓ)
    (hfree : FreeW us x ℓ (X₀ ++ Fw ++ X₁ ++ Tw ++ X₂)) :
    (∃ y, x ≤ X₀.length + y ∧ X₀.length + y ≤ x + ℓ ∧ y + L ≤ Fw.length ∧ FreeW us y L Fw) ∨
    (∃ y, x ≤ X₀.length + Fw.length + X₁.length + y ∧ X₀.length + Fw.length + X₁.length + y ≤ x + ℓ ∧
      y + L ≤ Tw.length ∧ FreeW us y L Tw) := by
  by_cases hF : L ≤ min (x + ℓ) (X₀.length + Fw.length) - max x X₀.length
  · left
    refine ⟨max x X₀.length - X₀.length, by omega, by omega, by omega, ?_⟩
    have e := seg_shift X₀ Fw (X₁ ++ Tw ++ X₂) (y := max x X₀.length - X₀.length) (L := L) (by omega)
    intro hc
    apply hfree
    rw [← e] at hc
    have : X₀ ++ Fw ++ (X₁ ++ Tw ++ X₂) = X₀ ++ Fw ++ X₁ ++ Tw ++ X₂ := by simp only [List.append_assoc]
    rw [this] at hc
    exact hc.trans (infix_drop_take _ (by omega) (by omega))
  · right
    have hT : L ≤ min (x + ℓ) (X₀.length + Fw.length + X₁.length + Tw.length) -
        max x (X₀.length + Fw.length + X₁.length) := by omega
    refine ⟨max x (X₀.length + Fw.length + X₁.length) - (X₀.length + Fw.length + X₁.length),
      by omega, by omega, by omega, ?_⟩
    have e := seg_shift (X₀ ++ Fw ++ X₁) Tw X₂
      (y := max x (X₀.length + Fw.length + X₁.length) - (X₀.length + Fw.length + X₁.length)) (L := L) (by omega)
    intro hc
    apply hfree
    rw [← e] at hc
    have hl : (X₀ ++ Fw ++ X₁).length = X₀.length + Fw.length + X₁.length := by simp only [List.length_append]
    rw [hl] at hc
    exact hc.trans (infix_drop_take _ (by omega) (by omega))

/-! ## §2 Counting positions -/

/-- At most `(r + 1) |Y|` positions `p ∈ [0, N)` have an element of `Y` in `[p, p + r]`. -/
theorem card_exists_le (N r : ℕ) (Y : Finset ℕ) :
    ((Finset.range N).filter (fun p => ∃ y ∈ Y, p ≤ y ∧ y ≤ p + r)).card ≤ (r + 1) * Y.card := by
  have hsub : (Finset.range N).filter (fun p => ∃ y ∈ Y, p ≤ y ∧ y ≤ p + r) ⊆
      Y.biUnion (fun y => Finset.Icc (y - r) y) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨y, hy, h1, h2⟩ := hp.2
    exact Finset.mem_biUnion.mpr ⟨y, hy, Finset.mem_Icc.mpr ⟨by omega, h1⟩⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
  calc ∑ y ∈ Y, (Finset.Icc (y - r) y).card ≤ ∑ _y ∈ Y, (r + 1) :=
        Finset.sum_le_sum (fun y _ => by rw [Nat.card_Icc]; omega)
    _ = (r + 1) * Y.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

namespace Setup

variable {Q : Type} [Fintype Q] [DecidableEq Q] {B : ValAuto Q} (S : Setup B)

/-- The length `Lr r := (ℓ₀(r) - C₀)/2` of a window without `u♯` inside a zone that a detour of range `r` requires. -/
def Lr (C₀ r : ℕ) : ℕ := (S.ell0 r - C₀) / 2

open Classical in
/-- The number of beginnings of windows of length `L` without `u♯` in the word `W`. -/
noncomputable def cntRun (L : ℕ) (W : List (Fin 2)) : ℕ :=
  ((Finset.range (W.length + 1)).filter (fun y => y + L ≤ W.length ∧ FreeW S.us y L W)).card

theorem xiI_le (i : S.Item) (r : ℕ) (ω : List (Fin 2)) (p : ℕ) :
    S.xiI i r ω p ≤ S.D.cP * (r + 1) ^ S.D.dP := by
  unfold xiI xiOf
  calc ind _ * S.D.g i.1 i.2.1 i.2.2 r ((ω.drop p).take r) ≤ 1 * S.D.g i.1 i.2.1 i.2.2 r ((ω.drop p).take r) :=
        Nat.mul_le_mul_right _ (ind_le_one _)
    _ ≤ _ := by rw [one_mul]; exact S.D.g_poly _ _ _ _ _

open Classical in
/-- **The sum over positions of the tail**: for the word `ω = X₀ F X₁ T X₂`, the sum over positions of the weights of the detours of the item `i` with range in `(J, N]`
is at most `Σ_r c_P (r+1)^{d_P} (r + 1)(cntRun F + cntRun T)`. -/
theorem tail_sum_le (i : S.Item) (J : ℕ) (X₀ Fw X₁ Tw X₂ : List (Fin 2))
    (hJ : ∀ r, J < r → 1 ≤ S.Lr (X₀.length + X₁.length + X₂.length) r) :
    ∑ p ∈ Finset.range (X₀ ++ Fw ++ X₁ ++ Tw ++ X₂).length,
      ∑ r ∈ Finset.Ioc J (X₀ ++ Fw ++ X₁ ++ Tw ++ X₂).length, (S.xiI i r (X₀ ++ Fw ++ X₁ ++ Tw ++ X₂) p : ℝ) ≤
    ∑ r ∈ Finset.Ioc J (X₀ ++ Fw ++ X₁ ++ Tw ++ X₂).length,
      (S.D.cP * (r + 1) ^ S.D.dP : ℕ) * ((r + 1 : ℕ) : ℝ) *
        ((S.cntRun (S.Lr (X₀.length + X₁.length + X₂.length) r) Fw : ℝ) +
          (S.cntRun (S.Lr (X₀.length + X₁.length + X₂.length) r) Tw : ℝ)) := by
  set ω := X₀ ++ Fw ++ X₁ ++ Tw ++ X₂
  set C₀ := X₀.length + X₁.length + X₂.length
  have hN : ω.length = X₀.length + Fw.length + X₁.length + Tw.length + X₂.length := by
    simp only [ω, List.length_append]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun r hr => ?_)
  have hr1 : 1 ≤ r := by have := (Finset.mem_Ioc.mp hr).1; omega
  have hL1 : 1 ≤ S.Lr C₀ r := hJ r (Finset.mem_Ioc.mp hr).1
  set L := S.Lr C₀ r
  set YF := ((Finset.range (Fw.length + 1)).filter (fun y => y + L ≤ Fw.length ∧ FreeW S.us y L Fw)).image
    (fun y => X₀.length + y)
  set YT := ((Finset.range (Tw.length + 1)).filter (fun y => y + L ≤ Tw.length ∧ FreeW S.us y L Tw)).image
    (fun y => X₀.length + Fw.length + X₁.length + y)
  -- the positions of the positive terms
  have hpos : ∀ p ∈ Finset.range ω.length, S.xiI i r ω p ≠ 0 →
      (∃ y ∈ YF, p ≤ y ∧ y ≤ p + r) ∨ (∃ y ∈ YT, p ≤ y ∧ y ≤ p + r) := by
    intro p hp hne
    unfold xiI xiOf at hne
    have hg : S.D.g i.1 i.2.1 i.2.2 r ((ω.drop p).take r) ≠ 0 := fun h => hne (by rw [h, mul_zero])
    have hlen := S.D.g_len _ _ _ _ _ hg
    rw [List.length_take, List.length_drop] at hlen
    obtain ⟨a, ha, hfree⟩ := S.free_of_g_ne i (v := (ω.drop p).take r) hg
    have hfree' : FreeW S.us (p + a) (S.ell0 r) ω := by
      intro hc; apply hfree
      have e : (((ω.drop p).take r).drop a).take (S.ell0 r) = (ω.drop (p + a)).take (S.ell0 r) := by
        rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]
      rw [e]; exact hc
    have hsplit := tail_split S.us X₀ Fw X₁ Tw X₂ L hL1 (x := p + a) (ℓ := S.ell0 r)
      (by rw [← hN]; omega) (by
        have hLd : L = (S.ell0 r - C₀) / 2 := rfl
        have hCd : C₀ = X₀.length + X₁.length + X₂.length := rfl
        omega) hfree'
    rcases hsplit with ⟨y, h1, h2, h3, h4⟩ | ⟨y, h1, h2, h3, h4⟩
    · left
      exact ⟨X₀.length + y, Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), h3, h4⟩, rfl⟩, by omega, by omega⟩
    · right
      exact ⟨X₀.length + Fw.length + X₁.length + y, Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), h3, h4⟩, rfl⟩, by omega, by omega⟩
  -- counting the sum
  have hcnt : ((Finset.range ω.length).filter (fun p => S.xiI i r ω p ≠ 0)).card ≤ (r + 1) * (YF.card + YT.card) := by
    have hsub : (Finset.range ω.length).filter (fun p => S.xiI i r ω p ≠ 0) ⊆
        (Finset.range ω.length).filter (fun p => ∃ y ∈ YF, p ≤ y ∧ y ≤ p + r) ∪
          (Finset.range ω.length).filter (fun p => ∃ y ∈ YT, p ≤ y ∧ y ≤ p + r) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rcases hpos p hp.1 hp.2 with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp.1, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp.1, h⟩)
    refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_union_le _ _) ?_)
    have := card_exists_le ω.length r YF
    have := card_exists_le ω.length r YT
    rw [mul_add]; omega
  have hYF : YF.card ≤ S.cntRun L Fw := Finset.card_image_le
  have hYT : YT.card ≤ S.cntRun L Tw := Finset.card_image_le
  calc ∑ p ∈ Finset.range ω.length, (S.xiI i r ω p : ℝ)
      = ∑ p ∈ (Finset.range ω.length).filter (fun p => S.xiI i r ω p ≠ 0), (S.xiI i r ω p : ℝ) :=
        (Finset.sum_filter_of_ne (fun p _ hp => by exact_mod_cast hp)).symm
    _ ≤ ∑ _p ∈ (Finset.range ω.length).filter (fun p => S.xiI i r ω p ≠ 0), ((S.D.cP * (r + 1) ^ S.D.dP : ℕ) : ℝ) :=
        Finset.sum_le_sum (fun p _ => by exact_mod_cast S.xiI_le i r ω p)
    _ = ((Finset.range ω.length).filter (fun p => S.xiI i r ω p ≠ 0)).card * ((S.D.cP * (r + 1) ^ S.D.dP : ℕ) : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((r + 1) * (S.cntRun L Fw + S.cntRun L Tw) : ℕ) * ((S.D.cP * (r + 1) ^ S.D.dP : ℕ) : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        exact_mod_cast le_trans hcnt (Nat.mul_le_mul_left _ (Nat.add_le_add hYF hYT))
    _ = _ := by push_cast; ring

end Setup

/-! ## §3 Windows in the Terras part ⇒ `RunMiss` -/

/-- The interval `[i₁, i₂)` of blocks has at most 11 (i₂ - i₁) bits. -/
theorem blockEnd_sub_le (β : List Bool) {i₁ i₂ : ℕ} (h12 : i₁ ≤ i₂) :
    blockEnd β i₂ ≤ blockEnd β i₁ + 11 * (i₂ - i₁) := by
  have e := htw_blockEnd_add β i₁ (i₂ - i₁)
  rw [Nat.add_sub_cancel' h12] at e
  rw [e]
  have h1 := (parityOf_length_bounds ((β.drop i₁).take (i₂ - i₁))).2
  have h2 : ((β.drop i₁).take (i₂ - i₁)).length ≤ i₂ - i₁ := by rw [List.length_take]; omega
  unfold htwLen
  omega

theorem blockEnd_mono (β : List Bool) {i₁ i₂ : ℕ} (h12 : i₁ ≤ i₂) : blockEnd β i₁ ≤ blockEnd β i₂ := by
  have e := htw_blockEnd_add β i₁ (i₂ - i₁)
  rw [Nat.add_sub_cancel' h12] at e
  omega

theorem bitsMSB_map_l2f : ∀ (m x : ℕ), (bitsMSB m x).map W3a.l2f = W2a.bitsF m x
  | 0, _ => rfl
  | m + 1, x => by
    simp only [bitsMSB, W2a.bitsF, List.map_cons]
    rw [bitsMSB_map_l2f m]
    congr 1
    have h : x / 2 ^ m % 2 < 2 := Nat.mod_lt _ (by norm_num)
    rcases (by omega : x / 2 ^ m % 2 = 0 ∨ x / 2 ^ m % 2 = 1) with h0 | h0 <;>
      simp [bitL, W3a.l2f, h0]

/-- The binary notation of `u♯`: `bitsMSB |u♯| (valW 0 u♯) = u♯` as a word of letters. -/
theorem bitsMSB_valW_eq (us : List (Fin 2)) : bitsMSB us.length (valW 0 us) = us.map bitLetter := by
  set w := bitsMSB us.length (valW 0 us) with hw
  have h1 : w.map W3a.l2f = us := by rw [hw, bitsMSB_map_l2f, W2a.bitsF_valW]
  have hd : IsDigits w := bitsMSB_isDigits us.length (valW 0 us)
  calc w = w.map (bitLetter ∘ W3a.l2f) := by
        conv_lhs => rw [← List.map_id w]
        refine List.map_congr_left (fun s hs => ?_)
        rcases hd s hs with rfl | rfl <;> rfl
    _ = (w.map W3a.l2f).map bitLetter := by rw [List.map_map]
    _ = us.map bitLetter := by rw [h1]

section Ter

variable (us : List (Fin 2)) (β₀ β' : List Bool) (n₁ a : ℕ)

/-- The property of cut words: containing `u♯` (the property passed to `GHit` of `W3b`). -/
def PU : Word → Prop := fun w => us.map bitLetter <:+: w

/-- The word of the Terras part (the top `m - s'` digits of the notation of `r_σ`, without the part of `β₀`, in `Fin 2`). -/
def TwOf : List (Fin 2) :=
  (bitsMSB ((parityOf (β₀ ++ β')).length - (parityOf β₀).length) (famRtop β₀ (β₀ ++ β'))).map W3a.l2f

theorem bitsMSB_split :
    bitsMSB (parityOf (β₀ ++ β')).length (terrasR (parityOf (β₀ ++ β'))) =
      bitsMSB ((parityOf (β₀ ++ β')).length - (parityOf β₀).length) (famRtop β₀ (β₀ ++ β')) ++
        bitsMSB (parityOf β₀).length (terrasR (parityOf β₀)) := by
  have hpre : β₀ <+: β₀ ++ β' := List.prefix_append _ _
  have hle := fam_s_le hpre
  have h1 := bitsMSB_add_mul ((parityOf (β₀ ++ β')).length - (parityOf β₀).length) (parityOf β₀).length
    (famRtop β₀ (β₀ ++ β')) (terrasR (parityOf β₀)) (fam_rtop_lt hpre) (terrasR_lt _)
  rw [Nat.sub_add_cancel hle, ← fam_terrasR_split hpre] at h1
  exact h1

theorem TwOf_length : (TwOf β₀ β').length = (parityOf (β₀ ++ β')).length - (parityOf β₀).length := by
  simp [TwOf, bitsMSB_length]

theorem blockEnd_b0 : blockEnd (β₀ ++ β') β₀.length = (parityOf β₀).length := by
  unfold blockEnd; rw [List.take_left' rfl]

theorem blockEnd_full : blockEnd (β₀ ++ β') (β₀.length + β'.length) = (parityOf (β₀ ++ β')).length := by
  unfold blockEnd; rw [List.take_of_length_le (by simp)]

/-- **A window that covers the cut of a group**: if a window `[y, y + L)` without `u♯` in the Terras part covers the range of bits of group `i`, then group `i` misses. -/
theorem not_gHit_of_cover {y L i : ℕ} (hfree : FreeW us y L (TwOf β₀ β'))
    (h1 : y ≤ (parityOf (β₀ ++ β')).length - blockEnd (β₀ ++ β') (β₀.length + (i + 1) * (n₁ + a)))
    (h2 : (parityOf (β₀ ++ β')).length - blockEnd (β₀ ++ β') (β₀.length + i * (n₁ + a)) ≤ y + L) :
    ¬ W3b.GHit (PU us) β₀.length n₁ a i (β₀ ++ β') := by
  have hca : β₀.length + i * (n₁ + a) + n₁ + a = β₀.length + (i + 1) * (n₁ + a) := by ring
  obtain ⟨X, Y, hW, hX⟩ := W3b.cutWord_segment (β₀ ++ β') (β₀.length + i * (n₁ + a) + n₁) a
  rw [hca] at hX
  intro hhit
  unfold W3b.GHit PU at hhit
  apply hfree
  have hadd := htw_blockEnd_add (β₀ ++ β') (β₀.length + i * (n₁ + a) + n₁) a
  rw [hca] at hadd
  have hcutlen : (W3b.cutWord a (β₀ ++ β') (β₀.length + i * (n₁ + a) + n₁)).length =
      htwLen a (β₀ ++ β') (β₀.length + i * (n₁ + a) + n₁) := W3b.cutWord_length _ _ _
  have hm : blockEnd (β₀ ++ β') (β₀.length + (i + 1) * (n₁ + a)) ≤ (parityOf (β₀ ++ β')).length :=
    blockEnd_le_full _ _
  have hb0c : (parityOf β₀).length ≤ blockEnd (β₀ ++ β') (β₀.length + i * (n₁ + a) + n₁) := by
    rw [← blockEnd_b0 β₀ β']; exact blockEnd_mono _ (by omega)
  have hic : blockEnd (β₀ ++ β') (β₀.length + i * (n₁ + a)) ≤ blockEnd (β₀ ++ β') (β₀.length + i * (n₁ + a) + n₁) :=
    blockEnd_mono _ (by omega)
  have hTw := TwOf_length β₀ β'
  -- the image under `l2f` of the cut word is a factor of `TwOf`
  set cut := W3b.cutWord a (β₀ ++ β') (β₀.length + i * (n₁ + a) + n₁)
  have hall : TwOf β₀ β' ++ (bitsMSB (parityOf β₀).length (terrasR (parityOf β₀))).map W3a.l2f =
      X.map W3a.l2f ++ cut.map W3a.l2f ++ Y.map W3a.l2f := by
    rw [← List.map_append, ← List.map_append, ← hW, bitsMSB_split β₀ β', List.map_append]
    rfl
  have h3 : ((TwOf β₀ β' ++ (bitsMSB (parityOf β₀).length (terrasR (parityOf β₀))).map W3a.l2f).drop X.length).take
      cut.length = cut.map W3a.l2f := by
    rw [hall, List.append_assoc, List.drop_left' (by simp), List.take_left' (by simp)]
  have hseg : cut.map W3a.l2f = ((TwOf β₀ β').drop X.length).take cut.length := by
    rw [← h3]; exact drop_take_append_left (by rw [hX, hcutlen, hTw]; omega)
  have hinf := hhit.map W3a.l2f
  rw [map_l2f_bitLetter, hseg] at hinf
  exact hinf.trans (infix_drop_take _ (by rw [hX]; omega) (by rw [hX, hcutlen]; omega))

end Ter

end Collatz.Arctic.NatQ5.W3h
