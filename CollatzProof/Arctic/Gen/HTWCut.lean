/-
The deterministic part of deriving the window frequencies `HTerrasWinR` from `HKeyTopR`.
Adapted from `HTWCut.lean` (the version for $T$). The residue `R` is an argument, and the only facts about residues used are the fields of `BlockModel`
`R_lt` (`R β < 2^m`) and `R_prefix` (the low digits of the residue of a concatenated sequence are the residue of the first part). The probabilistic part is in `Gen/HTWProb.lean`,
the main theorem in `Gen/HTWFromKey.lean`. The deterministic part of the proof of Theorem B.8.

* `htwDev`–`htw_combine`: the deviation of the empirical distribution of windows, and the assembly from chunks to an interval (independent of the residue; copied from the version for $T$).
* `htwR_append`: the general form of `terrasR_append` of the version for $T$ (there it is used only in existential form, and it follows from `R_prefix` and `R_lt`).
* The bits of the chunk `[a, a + K)` (positions `[m - L_{a+K}, m - L_a)` of the `m`-digit expansion of `R β`) are the `htwLen`-digit expansion of the quotient
  `htwVal R` of the residue up to the chunk divided by `2^{L_a}` (`htw_bits_split`). `L_i = blockEnd β i` and
  `m = (parityOf β).length` are **numbers of bits**; the number of steps of the map (`BlockModel.steps`) does not appear.
-/
import CollatzProof.Arctic.Gen.Model
import CollatzProof.Arctic.CoreWindow
import CollatzProof.Arctic.CoreX0
import CollatzProof.Arctic.CoreHelp
import CollatzProof.Arctic.WindowLLN

namespace Collatz.Arctic.Gen

open Collatz.Arctic
open Finset

/-! ## Deviation of the empirical distribution of windows (independent of the residue; copied from the version for $T$) -/

/-- Deviation from the uniform distribution of the empirical distribution of the windows of length `J` over the set `S` of starting positions (`|S|` times the sum of absolute differences). -/
def htwDev (w : Word) (J : ℕ) (S : Finset ℕ) : ℚ :=
  ∑ v ∈ wordsOfLen J, |∑ i ∈ S, ((if window w i J = v then (1 : ℚ) else 0) - 1 / 2 ^ J)|

theorem htw_dev_union (w : Word) (J : ℕ) {S S' : Finset ℕ} (h : Disjoint S S') :
    htwDev w J (S ∪ S') ≤ htwDev w J S + htwDev w J S' := by
  unfold htwDev
  rw [← sum_add_distrib]
  refine sum_le_sum (fun v _ => ?_)
  rw [sum_union h]
  exact abs_add_le _ _

theorem htw_dev_biUnion (w : Word) (J : ℕ) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (S : ι → Finset ℕ) (h : (s : Set ι).PairwiseDisjoint S) :
    htwDev w J (s.biUnion S) ≤ ∑ t ∈ s, htwDev w J (S t) := by
  unfold htwDev
  rw [sum_comm]
  refine sum_le_sum (fun v _ => ?_)
  rw [sum_biUnion h]
  exact abs_sum_le_sum_abs _ _

/-- The contribution of one window is at most 2. -/
lemma htw_dev_one (w : Word) (J i : ℕ) :
    ∑ v ∈ wordsOfLen J, |(if window w i J = v then (1 : ℚ) else 0) - 1 / 2 ^ J| ≤ 2 := by
  have hc : ∑ v ∈ wordsOfLen J, (if window w i J = v then (1 : ℚ) else 0) ≤ 1 := by
    rw [sum_boole]
    have : ((wordsOfLen J).filter (fun v => window w i J = v)).card ≤ 1 := by
      rw [filter_eq]
      split_ifs <;> simp
    exact_mod_cast this
  have hu : ∑ _v ∈ wordsOfLen J, (1 / 2 ^ J : ℚ) = 1 := by
    rw [sum_const, WinLLN.card_words, nsmul_eq_mul]
    push_cast
    field_simp
  calc ∑ v ∈ wordsOfLen J, |(if window w i J = v then (1 : ℚ) else 0) - 1 / 2 ^ J|
      ≤ ∑ v ∈ wordsOfLen J, ((if window w i J = v then (1 : ℚ) else 0) + 1 / 2 ^ J) := by
        refine sum_le_sum (fun v _ => (abs_sub _ _).trans ?_)
        rw [abs_of_nonneg (by split_ifs <;> norm_num), abs_of_nonneg (by positivity)]
    _ ≤ 2 := by rw [sum_add_distrib, hu]; linarith

/-- Trivial upper bound: the deviation is at most `2|S|`. -/
theorem htw_dev_le_card (w : Word) (J : ℕ) (S : Finset ℕ) : htwDev w J S ≤ 2 * S.card := by
  unfold htwDev
  calc ∑ v ∈ wordsOfLen J, |∑ i ∈ S, ((if window w i J = v then (1 : ℚ) else 0) - 1 / 2 ^ J)|
      ≤ ∑ v ∈ wordsOfLen J, ∑ i ∈ S, |(if window w i J = v then (1 : ℚ) else 0) - 1 / 2 ^ J| :=
        sum_le_sum (fun v _ => abs_sum_le_sum_abs _ _)
    _ = ∑ i ∈ S, ∑ v ∈ wordsOfLen J, |(if window w i J = v then (1 : ℚ) else 0) - 1 / 2 ^ J| :=
        sum_comm
    _ ≤ ∑ _i ∈ S, (2 : ℚ) := sum_le_sum (fun i _ => htw_dev_one w J i)
    _ = 2 * S.card := by rw [sum_const, nsmul_eq_mul]; ring

/-- The deviation written in terms of the number of windows in the interval `[a, b)`. -/
theorem htw_dev_Ico (w : Word) (a b J : ℕ) :
    htwDev w J (Ico a (b + 1 - J)) =
      ∑ v ∈ wordsOfLen J, |(winCount w a b J v : ℚ) - ((b + 1 - J - a : ℕ) : ℚ) / 2 ^ J| := by
  unfold htwDev
  refine sum_congr rfl (fun v _ => ?_)
  congr 1
  rw [sum_Ico_eq_sum_range, sum_sub_distrib, sum_boole, sum_const, card_range, nsmul_eq_mul,
    winCount_eq_card]
  ring

/-- Restatement of `WinClose`: the deviation is at most `2δN` (`N` is the number of windows). -/
theorem htw_winClose_iff {w : Word} {a b J : ℕ} {δ : ℚ} (hab : a + J ≤ b) (hb : b ≤ w.length) :
    WinClose w a b J δ ↔ htwDev w J (Ico a (b + 1 - J)) ≤ 2 * δ * ((b + 1 - J - a : ℕ) : ℚ) := by
  have hN : (0 : ℚ) < ((b + 1 - J - a : ℕ) : ℚ) := by
    exact_mod_cast (show 0 < b + 1 - J - a by omega)
  rw [htw_dev_Ico]
  have e : ∑ v ∈ wordsOfLen J, |(winCount w a b J v : ℚ) / ((b + 1 - J - a : ℕ) : ℚ) - 1 / 2 ^ J| =
      (∑ v ∈ wordsOfLen J, |(winCount w a b J v : ℚ) - ((b + 1 - J - a : ℕ) : ℚ) / 2 ^ J|) /
        ((b + 1 - J - a : ℕ) : ℚ) := by
    rw [sum_div]
    refine sum_congr rfl (fun v _ => ?_)
    rw [show (winCount w a b J v : ℚ) / ((b + 1 - J - a : ℕ) : ℚ) - 1 / 2 ^ J =
        ((winCount w a b J v : ℚ) - ((b + 1 - J - a : ℕ) : ℚ) / 2 ^ J) /
          ((b + 1 - J - a : ℕ) : ℚ) by field_simp, abs_div, abs_of_pos hN]
  unfold WinClose
  rw [e, div_le_iff₀ hN]
  exact ⟨fun h => h.2.2, fun h => ⟨hab, hb, h⟩⟩

/-- The deviation of windows of length 0 is 0. -/
theorem htw_dev_zero (w : Word) (S : Finset ℕ) : htwDev w 0 S = 0 := by
  unfold htwDev
  refine sum_eq_zero (fun v hv => ?_)
  have hv0 : v = [] := List.eq_nil_of_length_eq_zero (length_of_mem_wordsOfLen hv)
  have hw : ∀ i, window w i 0 = v := fun i => by rw [hv0]; simp [window]
  simp [hw]

/-! ## From chunks to an interval (independent of the residue; copied from the version for $T$) -/

/-- If `p` is decreasing on `[0, T]`, then `p t ≤ p s` for `s ≤ t ≤ T`. -/
lemma htw_anti {p : ℕ → ℕ} {T : ℕ} (h : ∀ t < T, p (t + 1) ≤ p t) {s t : ℕ} (hst : s ≤ t)
    (htT : t ≤ T) : p t ≤ p s := by
  induction t with
  | zero => rw [Nat.le_zero.mp hst]
  | succ t ih =>
    rcases Nat.eq_or_lt_of_le hst with rfl | hlt
    · exact le_rfl
    · exact (h t (by omega)).trans (ih (by omega) (by omega))

/-- Telescoping sum. -/
lemma htw_telescope {p : ℕ → ℕ} : ∀ {T : ℕ}, (∀ t < T, p (t + 1) ≤ p t) →
    ∑ t ∈ range T, (p t - p (t + 1)) + p T = p 0
  | 0, _ => by simp
  | T + 1, h => by
    rw [sum_range_succ]
    have h1 := htw_telescope (T := T) (fun t ht => h t (by omega))
    have h2 := h T (by omega)
    omega

/-- **From chunks to an interval**: split the interval `[A, p 0)` into the chunks `[p (t+1), p t)` (`t < T`) and the leftover `[A, p T)`. If the window
frequencies of the good chunks (`t ∈ G`) are within `δ'`, the total deviation is at most `2δ'N` plus twice the sum of the lengths of the leftover and of the bad chunks and the windows across the boundaries
(at most `TJ` of them). -/
theorem htw_combine (w : Word) {J : ℕ} (hJ : 1 ≤ J) {δ' : ℚ} (hδ' : 0 ≤ δ') {A T : ℕ} {p : ℕ → ℕ}
    (hanti : ∀ t < T, p (t + 1) ≤ p t) (hA : A ≤ p T)
    (G : Finset ℕ) (hG : G ⊆ range T) (hgood : ∀ t ∈ G, WinClose w (p (t + 1)) (p t) J δ') :
    htwDev w J (Ico A (p 0 + 1 - J)) ≤
      2 * δ' * ((p 0 + 1 - J - A : ℕ) : ℚ) +
        2 * ((p T - A + ∑ t ∈ range T \ G, (p t - p (t + 1)) + T * J + 1 : ℕ) : ℚ) := by
  set S := Ico A (p 0 + 1 - J) with hS
  set St : ℕ → Finset ℕ := fun t => Ico (p (t + 1)) (p t + 1 - J) with hSt
  set U := G.biUnion St with hU
  have hsub : ∀ t ∈ G, St t ⊆ S := by
    intro t ht x hx
    have htT := mem_range.mp (hG ht)
    have h1 : p T ≤ p (t + 1) := htw_anti hanti (by omega) le_rfl
    have h2 : p t ≤ p 0 := htw_anti hanti (Nat.zero_le _) (by omega)
    rw [hSt, mem_Ico] at hx
    rw [hS, mem_Ico]
    omega
  have hUS : U ⊆ S := biUnion_subset.mpr hsub
  have hdisj : (G : Set ℕ).PairwiseDisjoint St := by
    intro s hs t ht hst
    rw [Function.onFun, disjoint_left]
    intro x hxs hxt
    have hs' := mem_range.mp (hG hs)
    have ht' := mem_range.mp (hG ht)
    rw [hSt, mem_Ico] at hxs hxt
    rcases Nat.lt_or_gt_of_ne hst with h | h
    · have := htw_anti hanti (show s + 1 ≤ t by omega) (by omega : t ≤ T)
      omega
    · have := htw_anti hanti (show t + 1 ≤ s by omega) (by omega : s ≤ T)
      omega
  have hcardSt : ∀ t, (St t).card = p t + 1 - J - p (t + 1) := fun t => by
    rw [hSt, Nat.card_Ico]
  -- split
  have hd1 : htwDev w J S ≤ htwDev w J U + htwDev w J (S \ U) := by
    have e : S = U ∪ (S \ U) := (union_sdiff_of_subset hUS).symm
    conv_lhs => rw [e]
    exact htw_dev_union w J disjoint_sdiff
  have hd2 : htwDev w J U ≤ ∑ t ∈ G, 2 * δ' * ((St t).card : ℚ) := by
    refine (htw_dev_biUnion w J G St hdisj).trans (sum_le_sum (fun t ht => ?_))
    have hw := hgood t ht
    rw [hcardSt]
    exact (htw_winClose_iff hw.1 hw.2.1).mp hw
  have hcardU : U.card = ∑ t ∈ G, (St t).card := card_biUnion hdisj
  have hd3 : htwDev w J (S \ U) ≤ 2 * ((S \ U).card : ℚ) := htw_dev_le_card w J _
  have hcardSU : (S \ U).card = S.card - U.card := card_sdiff_of_subset hUS
  have hUleS : U.card ≤ S.card := card_le_card hUS
  have hcardS : S.card = p 0 + 1 - J - A := by rw [hS, Nat.card_Ico]
  -- counting: `|S| ≤ |U| + remainder`
  have hcount : S.card ≤ U.card + (p T - A + ∑ t ∈ range T \ G, (p t - p (t + 1)) + T * J + 1) := by
    have htel := htw_telescope hanti
    have hsd := sum_sdiff (f := fun t => p t - p (t + 1)) hG
    have hGle : ∑ t ∈ G, (p t - p (t + 1)) ≤ ∑ t ∈ G, ((St t).card + J) := by
      refine sum_le_sum (fun t ht => ?_)
      have hw := (hgood t ht).1
      rw [hcardSt]
      omega
    rw [sum_add_distrib, sum_const, smul_eq_mul, ← hcardU] at hGle
    have hGc : G.card ≤ T := by
      have := card_le_card hG
      rwa [card_range] at this
    have hGJ : G.card * J ≤ T * J := Nat.mul_le_mul_right J hGc
    have h0 : p T ≤ p 0 := htw_anti hanti (Nat.zero_le _) le_rfl
    rw [hcardS]
    omega
  have hSUle : (S \ U).card ≤ p T - A + ∑ t ∈ range T \ G, (p t - p (t + 1)) + T * J + 1 := by
    rw [hcardSU]; omega
  -- conclusion
  have hsumU : ∑ t ∈ G, 2 * δ' * ((St t).card : ℚ) ≤ 2 * δ' * ((p 0 + 1 - J - A : ℕ) : ℚ) := by
    rw [← mul_sum, ← hcardS]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have : ((U.card : ℕ) : ℚ) = ∑ t ∈ G, ((St t).card : ℚ) := by rw [hcardU]; push_cast; rfl
    rw [← this]
    exact_mod_cast hUleS
  have hrest : 2 * ((S \ U).card : ℚ) ≤
      2 * ((p T - A + ∑ t ∈ range T \ G, (p t - p (t + 1)) + T * J + 1 : ℕ) : ℚ) := by
    have : ((S \ U).card : ℚ) ≤
        ((p T - A + ∑ t ∈ range T \ G, (p t - p (t + 1)) + T * J + 1 : ℕ) : ℚ) := by
      exact_mod_cast hSUle
    linarith
  linarith

/-! ## Residues of concatenations (from `R_lt` and `R_prefix`) -/

section Cut

variable (R : List Bool → ℕ)

/-- **Residue of a concatenated sequence** (the general form of `terrasR_append`): `R (β₁ ++ β₂)` is `R β₁` plus `2^{m(β₁)}` times
a number with `m(β₂)` digits. -/
theorem htwR_append (hlt : ∀ β, R β < 2 ^ (parityOf β).length)
    (hpre : ∀ β₁ β₂, R (β₁ ++ β₂) % 2 ^ (parityOf β₁).length = R β₁) (β₁ β₂ : List Bool) :
    ∃ r' < 2 ^ (parityOf β₂).length,
      R (β₁ ++ β₂) = R β₁ + 2 ^ (parityOf β₁).length * r' := by
  refine ⟨R (β₁ ++ β₂) / 2 ^ (parityOf β₁).length, ?_, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    have h := hlt (β₁ ++ β₂)
    rw [fam_parityOf_append, List.length_append] at h
    rwa [Nat.add_comm (parityOf β₂).length]
  · conv_lhs => rw [← Nat.mod_add_div (R (β₁ ++ β₂)) (2 ^ (parityOf β₁).length)]
    rw [hpre]

/-! ## Chunks of block indices -/

/-- The quantity of `HKeyTopR`: the quotient of the residue of `β₀ ++ β ++ γ` by `2^{|parityOf (β₀ ++ β)|}` (the bits of the part `γ`). -/
def htwCutVal (β₀ β γ : List Bool) : ℕ :=
  R (β₀ ++ β ++ γ) / 2 ^ (parityOf (β₀ ++ β)).length

/-- The value of the chunk `[a, a + K)` of block indices: the quotient of the residue up to the end of the chunk by `2^{L_a}`. -/
def htwVal (K : ℕ) (β : List Bool) (a : ℕ) : ℕ :=
  R (β.take (a + K)) / 2 ^ (parityOf (β.take a)).length

/-- The number of bits of the chunk `[a, a + K)` (independent of the residue). -/
def htwLen (K : ℕ) (β : List Bool) (a : ℕ) : ℕ := (parityOf ((β.drop a).take K)).length

/-- The chunk `[a, a + K)` is good: the window frequencies of the bits of the chunk are within `δ` of uniform. -/
def htwGood (K J : ℕ) (δ : ℚ) (β : List Bool) (a : ℕ) : Prop :=
  WinClose (bitsMSB (htwLen K β a) (htwVal R K β a)) 0 (htwLen K β a) J δ

theorem htw_blockEnd_add (β : List Bool) (a K : ℕ) :
    blockEnd β (a + K) = blockEnd β a + htwLen K β a := by
  unfold blockEnd htwLen
  rw [List.take_add, fam_parityOf_append, List.length_append]

/-- The interval `[i, i + d)` of block indices (contained in `β`) has at least `8d` bits. -/
theorem htw_blockEnd_ge (β : List Bool) (i d : ℕ) (h : i + d ≤ β.length) :
    blockEnd β i + 8 * d ≤ blockEnd β (i + d) := by
  rw [htw_blockEnd_add]
  have h1 := (parityOf_length_bounds ((β.drop i).take d)).1
  have h2 : ((β.drop i).take d).length = d := by
    rw [List.length_take, List.length_drop]; omega
  unfold htwLen
  omega

/-- The value of a chunk fits in as many digits as the number of bits of the part `γ` (uses only `R_lt`). -/
theorem htwCutVal_lt (hlt : ∀ β, R β < 2 ^ (parityOf β).length) (β₀ β γ : List Bool) :
    htwCutVal R β₀ β γ < 2 ^ (parityOf γ).length := by
  unfold htwCutVal
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
  have h := hlt (β₀ ++ β ++ γ)
  rw [fam_parityOf_append (β₀ ++ β) γ, List.length_append] at h
  rwa [Nat.add_comm (parityOf γ).length]

/-- The expansion of the residue of a sequence split into three parts is the expansions of the parts `β₃`, `β₂` (the value of the chunk) and `β₁`, from the most significant. -/
theorem htw_bits_split_aux (hlt : ∀ β, R β < 2 ^ (parityOf β).length)
    (hpre : ∀ β₁ β₂, R (β₁ ++ β₂) % 2 ^ (parityOf β₁).length = R β₁) (β₁ β₂ β₃ : List Bool) :
    ∃ X Y : Word, bitsMSB (parityOf (β₁ ++ β₂ ++ β₃)).length (R (β₁ ++ β₂ ++ β₃)) =
      X ++ bitsMSB (parityOf β₂).length (R (β₁ ++ β₂) / 2 ^ (parityOf β₁).length) ++ Y ∧
      X.length = (parityOf (β₁ ++ β₂ ++ β₃)).length -
        ((parityOf β₁).length + (parityOf β₂).length) := by
  obtain ⟨r₂, hr₂, h12⟩ := htwR_append R hlt hpre β₁ β₂
  obtain ⟨r₃, hr₃, h123⟩ := htwR_append R hlt hpre (β₁ ++ β₂) β₃
  have hval : R (β₁ ++ β₂) / 2 ^ (parityOf β₁).length = r₂ := by
    rw [h12, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (hlt β₁), zero_add]
  have hL12 : (parityOf (β₁ ++ β₂)).length = (parityOf β₁).length + (parityOf β₂).length := by
    rw [fam_parityOf_append, List.length_append]
  have hm : (parityOf (β₁ ++ β₂ ++ β₃)).length =
      ((parityOf β₃).length + (parityOf β₂).length) + (parityOf β₁).length := by
    rw [fam_parityOf_append, List.length_append, hL12]; omega
  have hR : R (β₁ ++ β₂ ++ β₃) =
      R β₁ + 2 ^ (parityOf β₁).length * (r₂ + 2 ^ (parityOf β₂).length * r₃) := by
    rw [h123, h12, hL12, pow_add]; ring
  have hlt' : r₂ + 2 ^ (parityOf β₂).length * r₃ <
      2 ^ ((parityOf β₃).length + (parityOf β₂).length) := by
    have : 2 ^ (parityOf β₂).length * (r₃ + 1) ≤
        2 ^ (parityOf β₂).length * 2 ^ (parityOf β₃).length := Nat.mul_le_mul_left _ hr₃
    rw [pow_add, mul_comm (2 ^ (parityOf β₃).length)]
    rw [mul_add, mul_one] at this
    omega
  refine ⟨bitsMSB (parityOf β₃).length r₃, bitsMSB (parityOf β₁).length (R β₁), ?_, ?_⟩
  · rw [hR, hm, bitsMSB_add_mul _ _ _ _ hlt' (hlt β₁), bitsMSB_add_mul _ _ _ _ hr₃ hr₂, hval]
  · rw [bitsMSB_length, hm]
    omega

/-- **The bits of a chunk** (Terras consistency): the `m`-digit expansion of `R β` is `X ++ (expansion of the value of the chunk) ++ Y`, with
`|X| = m - L_{a+K}`. -/
theorem htw_bits_split (hlt : ∀ β, R β < 2 ^ (parityOf β).length)
    (hpre : ∀ β₁ β₂, R (β₁ ++ β₂) % 2 ^ (parityOf β₁).length = R β₁) (β : List Bool) (a K : ℕ) :
    ∃ X Y : Word, bitsMSB (parityOf β).length (R β) =
      X ++ bitsMSB (htwLen K β a) (htwVal R K β a) ++ Y ∧
      X.length = (parityOf β).length - blockEnd β (a + K) := by
  have hβ : β.take a ++ (β.drop a).take K ++ β.drop (a + K) = β := by
    rw [← List.take_add, List.take_append_drop]
  have hEnd : blockEnd β (a + K) =
      (parityOf (β.take a)).length + (parityOf ((β.drop a).take K)).length := by
    unfold blockEnd; rw [List.take_add, fam_parityOf_append, List.length_append]
  have hvdef : htwVal R K β a =
      R (β.take a ++ (β.drop a).take K) / 2 ^ (parityOf (β.take a)).length := by
    unfold htwVal; rw [List.take_add]
  have hldef : htwLen K β a = (parityOf ((β.drop a).take K)).length := rfl
  have h := htw_bits_split_aux R hlt hpre (β.take a) ((β.drop a).take K) (β.drop (a + K))
  rw [hβ] at h
  rw [hEnd, hvdef, hldef]
  exact h

/-- The window frequencies of a good chunk are the window frequencies of positions `[m - L_{a+K}, m - L_a)` in the expansion of `R β`. -/
theorem htw_good_win (hlt : ∀ β, R β < 2 ^ (parityOf β).length)
    (hpre : ∀ β₁ β₂, R (β₁ ++ β₂) % 2 ^ (parityOf β₁).length = R β₁)
    {K J : ℕ} {δ : ℚ} {β : List Bool} {a : ℕ} (h : htwGood R K J δ β a) :
    WinClose (bitsMSB (parityOf β).length (R β))
      ((parityOf β).length - blockEnd β (a + K)) ((parityOf β).length - blockEnd β a) J δ := by
  obtain ⟨X, Y, hw, hX⟩ := htw_bits_split R hlt hpre β a K
  have hle : blockEnd β (a + K) ≤ (parityOf β).length := blockEnd_le_full β _
  rw [htw_blockEnd_add] at hle hX
  have e1 : (parityOf β).length - blockEnd β (a + K) = X.length + 0 := by
    rw [htw_blockEnd_add]; omega
  have e2 : (parityOf β).length - blockEnd β a = X.length + htwLen K β a := by omega
  rw [e1, e2, hw]
  exact (winClose_append_shift X _ Y (by rw [bitsMSB_length]) δ).mpr h

/-- Whether a chunk is good depends only on the blocks up to the end of the chunk. -/
theorem htw_good_take (K J : ℕ) (δ : ℚ) (β : List Bool) (a : ℕ) :
    htwGood R K J δ (β.take (a + K)) a ↔ htwGood R K J δ β a := by
  have h1 : htwLen K (β.take (a + K)) a = htwLen K β a := by
    unfold htwLen
    rw [List.drop_take, List.take_take, show min K (a + K - a) = K by omega]
  have h2 : htwVal R K (β.take (a + K)) a = htwVal R K β a := by
    unfold htwVal
    rw [List.take_take, List.take_take, min_self, min_eq_left (by omega)]
  unfold htwGood
  rw [h1, h2]

/-- Goodness of a chunk written in terms of the quantity of `HKeyTopR`. -/
theorem htw_good_cut (K J : ℕ) (δ : ℚ) (β₀ β₁ γ : List Bool) (hγ : γ.length = K) :
    htwGood R K J δ (β₀ ++ β₁ ++ γ) (β₀ ++ β₁).length ↔
      WinClose (bitsMSB (parityOf γ).length (htwCutVal R β₀ β₁ γ)) 0 (parityOf γ).length J δ := by
  have h1 : htwLen K (β₀ ++ β₁ ++ γ) (β₀ ++ β₁).length = (parityOf γ).length := by
    unfold htwLen
    rw [List.drop_left, List.take_of_length_le (by omega)]
  have h2 : htwVal R K (β₀ ++ β₁ ++ γ) (β₀ ++ β₁).length = htwCutVal R β₀ β₁ γ := by
    unfold htwVal htwCutVal
    rw [List.take_left, List.take_of_length_le (by simp only [List.length_append]; omega)]
  unfold htwGood
  rw [h1, h2]

end Cut

end Collatz.Arctic.Gen
