/-
The main inequality (a step of the proof of `MinRate` in the general case: Theorem B.3, Step 7).

We bound the sum, over the joined words, of the variance `pvar (sV)` of the ideal lineage values in two ways.
* From above: by the sum identity `hsp_sV_var` it is at most `(n+1) · (number of joined words) · r (M (L + |u|))²` (the variance of each segment is bounded).
* From below: if all segments are good and the spread is at least `κ |W|`, then `spr W ≤ (difference of lineage values) + 2Mh + 2M|u|`
  (`hsp_spr_le_lin`) and the difference between the true and the ideal values (`hsp_sV_err`) give `pvar (sV) ≥ T²/4 - r n² J²`
  (`T = κ (n+1) L - 2Mh - 2M|u|`; `Δ_gap` and `Ψ = T²/4 - r n² J²` in the paper). Joined words containing a segment that is not good form a fraction at most `(n+1) 2 q^{⌊h/|u|⌋}`, and those with
  small spread a fraction at most `δ 2^{n·jwMax}` (from the lower tail `κ` over uniform words, `hsp_word_sum`).
-/
import CollatzProof.Arctic.HSPSpread

namespace Collatz.Arctic

open MinIdeal Matrix Arc Classical

variable {D : ℕ} {A : Interp D} {C : Finset (Fin D)} (S : LinSetup A C)

lemma hsp_sWord_len {L : ℕ} {x₀ : Word} (hx₀ : x₀.length = L) :
    ∀ {ps : PList S}, (∀ gx ∈ ps, gx.2.length = L) → (ps.length + 1) * L ≤ (sWord S x₀ ps).length
  | [], _ => by simp [sWord, hx₀]
  | (g, x) :: ps, hps => by
    have ih := hsp_sWord_len hx₀ (fun gx hgx => hps gx (List.mem_cons_of_mem _ hgx))
    have hx := hps (g, x) List.mem_cons_self
    simp only [sWord, List.length_append, List.length_cons]
    simp only at hx
    nlinarith

/-- **The main inequality**. -/
theorem hsp_main_ineq (hSC : StrongConnIn A C) (hND : NeverDies A C C) (n L h N₀ : ℕ)
    (hh : 2 * h ≤ L) (hL : N₀ ≤ L) (κ δ : ℝ) (hκ : 0 < κ) (hδ : 0 ≤ δ)
    (hlow : ∀ N, N₀ ≤ N → ((((wordsOfLen N).filter (fun W => (spr A C W : ℝ) < κ * N)).card : ℕ) : ℝ)
      ≤ δ * 2 ^ N)
    (T : ℝ) (hT : T = κ * (n + 1) * L - 2 * (digMax A * h : ℕ) - 2 * (digMax A * S.u.length : ℕ))
    (hT0 : 0 ≤ T)
    (hΦ : 0 ≤ T ^ 2 / 4 - Fintype.card (Cls S.E S.hE) * (n * (junErr S h : ℝ)) ^ 2) :
    (T ^ 2 / 4 - Fintype.card (Cls S.E S.hE) * (n * (junErr S h : ℝ)) ^ 2) *
      (1 - (n + 1) * (2 * ((1 - 1 / 2 ^ S.u.length : ℚ) : ℝ) ^ (h / S.u.length)) -
        δ * 2 ^ (n * jwMax S)) ≤
      (n + 1) * Fintype.card (Cls S.E S.hE) * ((digMax A : ℝ) * (L + S.u.length)) ^ 2 := by
  set r : ℝ := (Fintype.card (Cls S.E S.hE) : ℝ) with hr
  set J : ℝ := (junErr S h : ℝ) with hJ
  set Φ : ℝ := T ^ 2 / 4 - r * (n * J) ^ 2 with hΦdef
  set G : ℝ := ((realSet S).card : ℝ) with hG
  set M : ℝ := (digMax A : ℝ) with hM
  set U : ℕ := S.u.length with hU
  set q : ℝ := ((1 - 1 / 2 ^ U : ℚ) : ℝ) with hq
  set Tot : ℝ := 2 ^ L * (G * 2 ^ L) ^ n with hTot
  have hTotpos : 0 < Tot := by
    have : (1 : ℝ) ≤ G := by
      have := Finset.card_pos.mpr ⟨1, (hsp_mem_realSet S).mpr (hsp_realized_one S)⟩
      rw [hG]; exact_mod_cast this
    positivity
  -- indicator functions
  let I1 : Word → PList S → ℝ := fun x₀ ps => if AllGood S h x₀ ps then 0 else 1
  let F : Word → ℝ := fun W => if (spr A C W : ℝ) < κ * W.length then 1 else 0
  -- pointwise lower bound
  have hpt : ∀ x₀ ∈ wordsOfLen L, ∀ ps ∈ PS S L n,
      Φ * (1 - I1 x₀ ps - F (sWord S x₀ ps)) ≤ pvar (sV S h x₀ ps) := by
    intro x₀ hx₀ ps hps
    have hok := hsp_PS_allOk S L hx₀ hps
    have hpv := hsp_pvar_nonneg (sV S h x₀ ps)
    by_cases hg : AllGood S h x₀ ps
    · by_cases hb : (spr A C (sWord S x₀ ps) : ℝ) < κ * (sWord S x₀ ps).length
      · simp only [I1, F, hg, hb, ↓reduceIte]; nlinarith
      · simp only [I1, F, hg, hb, ↓reduceIte, sub_zero, mul_one]
        push Not at hb
        -- spread and the difference of lineage values
        have hW := hsp_sWord_eq S h hg
        have hPd := (hsp_segDec_digits S h hok.1).1
        have hKd := hsp_sK_digits S h hok
        have hQd := hsp_sQ_digits S h hok
        have hPl := (hsp_segDec_len S h x₀).1
        have hQl := hsp_sQ_len S h x₀ ps
        obtain ⟨j₁, j₂, hj⟩ := hsp_spr_le_lin S hND hPd hKd hQd hPl hQl
        rw [← hW] at hj
        -- lengths
        have hlen := hsp_sWord_len S (length_of_mem_wordsOfLen hx₀)
          (fun gx hgx => length_of_mem_wordsOfLen ((hsp_PS_mem S L hps).2 gx hgx).2)
        rw [(hsp_PS_mem S L hps).1] at hlen
        have hlenR : ((n + 1) * L : ℝ) ≤ (sWord S x₀ ps).length := by exact_mod_cast hlen
        have hκW : κ * ((n + 1) * L) ≤ κ * (sWord S x₀ ps).length :=
          mul_le_mul_of_nonneg_left hlenR hκ.le
        -- the difference is at least `T`
        set v := prof S (sK S h x₀ ps)
        have hD : T ≤ v j₁ - v j₂ := by
          simp only [v, prof]; rw [hT]; push_cast at hj ⊢; nlinarith
        have hD2 : T ^ 2 ≤ (v j₁ - v j₂) ^ 2 := pow_le_pow_left₀ hT0 hD 2
        have h1 := hsp_pvar_ge v j₁ j₂
        have herr := hsp_sV_err S h hok
        rw [(hsp_PS_mem S L hps).1] at herr
        have h2 := hsp_pvar_perturb v (sV S h x₀ ps) (n * J) (fun i => herr i)
        rw [hΦdef]
        nlinarith
    · simp only [I1, F, hg, ↓reduceIte]
      split_ifs <;> nlinarith
  -- sum
  have hsum := Finset.sum_le_sum (fun x₀ hx₀ => Finset.sum_le_sum (fun ps hps => hpt x₀ hx₀ ps hps))
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib] at hsum
  -- number of joined words
  have hcount : ∑ x₀ ∈ wordsOfLen L, ∑ _ps ∈ PS S L n, Φ = Φ * Tot := by
    simp only [Finset.sum_const, WinLLN.card_words, nsmul_eq_mul]
    rw [hsp_PS_card]; push_cast; rw [hTot]; ring
  -- joined words that are not all good
  have hng := hsp_count_notGood S h L n
  have hcng := hsp_card_not_good S L h hh
  have hng' : ∑ x₀ ∈ wordsOfLen L, ∑ ps ∈ PS S L n, Φ * I1 x₀ ps ≤
      Φ * ((n + 1) * (2 * q ^ (h / U)) * Tot) := by
    simp only [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (hng.trans ?_) hΦ
    have := (Rat.cast_le (K := ℝ)).mpr hcng
    push_cast at this
    rw [hTot]
    have hc : (0 : ℝ) ≤ (n + 1) * (G * 2 ^ L) ^ n := by positivity
    calc (n + 1 : ℝ) * (G * 2 ^ L) ^ n * (((wordsOfLen L).filter (fun x => ¬ GoodSeg S h x)).card : ℝ)
        ≤ (n + 1) * (G * 2 ^ L) ^ n * (2 * (2 ^ L * q ^ (h / U))) :=
          mul_le_mul_of_nonneg_left (by rw [hq]; push_cast; exact this) hc
      _ = _ := by ring
  -- joined words with small spread
  have hF0 : ∀ W, 0 ≤ F W := fun W => by simp only [F]; split_ifs <;> norm_num
  have hFb : ∀ N, N₀ ≤ N → ∑ W ∈ wordsOfLen N, F W ≤ δ * 2 ^ (N + 0) := by
    intro N hN
    have e : ∑ W ∈ wordsOfLen N, F W =
        ((((wordsOfLen N).filter (fun W => (spr A C W : ℝ) < κ * N)).card : ℕ) : ℝ) := by
      simp only [F]
      rw [← Finset.sum_boole]
      refine Finset.sum_congr rfl (fun W hW => ?_)
      rw [length_of_mem_wordsOfLen hW]
    rw [e, Nat.add_zero]
    exact hlow N hN
  have hws := hsp_word_sum S L N₀ δ hδ hL n F 0 hF0 hFb
  have hbad : ∑ x₀ ∈ wordsOfLen L, ∑ ps ∈ PS S L n, Φ * F (sWord S x₀ ps) ≤
      Φ * (δ * 2 ^ (n * jwMax S) * Tot) := by
    simp only [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (hws.trans (le_of_eq ?_)) hΦ
    rw [hTot, hG, Nat.add_zero, mul_pow, show (n + 1) * L = L + L * n by ring, pow_add, pow_add,
      pow_mul]
    ring
  -- from above
  have hvar := hsp_sV_var S h L hSC n
  have hpx : ∀ x ∈ wordsOfLen L, pvar (prof S (segDec S h x).2.1) ≤ r * (M * (L + U)) ^ 2 := by
    intro x hx
    refine hsp_pvar_le _ _ (fun i => Nat.cast_nonneg _) (fun i => ?_)
    have hc := (hsp_segDec_digits S h (WinLLN.bin_of_mem hx)).2.1
    have h1 := hsp_lin_bound S i hc
    have h2 := (hsp_segDec_len S h x).2.2
    rw [length_of_mem_wordsOfLen hx] at h2
    have h3 : linVal S i (segDec S h x).2.1 ≤ digMax A * (L + U) :=
      h1.trans (Nat.mul_le_mul_left _ (by omega))
    simp only [prof]
    rw [hM]
    exact_mod_cast h3
  have hup : ∑ x₀ ∈ wordsOfLen L, ∑ ps ∈ PS S L n, pvar (sV S h x₀ ps) ≤
      (n + 1) * Tot * (r * (M * (L + U)) ^ 2) := by
    rw [hvar]
    have h1 : ∑ x ∈ wordsOfLen L, pvar (prof S (segDec S h x).2.1) ≤
        2 ^ L * (r * (M * (L + U)) ^ 2) := by
      calc _ ≤ ∑ _x ∈ wordsOfLen L, r * (M * (L + U)) ^ 2 := Finset.sum_le_sum hpx
        _ = _ := by rw [Finset.sum_const, WinLLN.card_words, nsmul_eq_mul]; push_cast; ring
    have hc : (0 : ℝ) ≤ (n + 1) * (G * 2 ^ L) ^ n := by positivity
    calc (n + 1 : ℝ) * (G * 2 ^ L) ^ n * ∑ x ∈ wordsOfLen L, pvar (prof S (segDec S h x).2.1)
        ≤ (n + 1) * (G * 2 ^ L) ^ n * (2 ^ L * (r * (M * (L + U)) ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 hc
      _ = _ := by rw [hTot]; ring
  -- conclusion
  rw [hcount] at hsum
  have hfin : Φ * Tot * (1 - (n + 1) * (2 * q ^ (h / U)) - δ * 2 ^ (n * jwMax S)) ≤
      (n + 1) * Tot * (r * (M * (L + U)) ^ 2) := by
    have e : Φ * Tot * (1 - (n + 1) * (2 * q ^ (h / U)) - δ * 2 ^ (n * jwMax S)) =
        Φ * Tot - Φ * ((n + 1) * (2 * q ^ (h / U)) * Tot) - Φ * (δ * 2 ^ (n * jwMax S) * Tot) := by
      ring
    rw [e]
    linarith
  have e1 : Φ * Tot * (1 - (n + 1) * (2 * q ^ (h / U)) - δ * 2 ^ (n * jwMax S)) =
      Tot * (Φ * (1 - (n + 1) * (2 * q ^ (h / U)) - δ * 2 ^ (n * jwMax S))) := by ring
  have e2 : (n + 1) * Tot * (r * (M * (L + U)) ^ 2) = Tot * ((n + 1) * r * (M * (L + U)) ^ 2) := by ring
  rw [e1, e2] at hfin
  exact le_of_mul_le_mul_left hfin hTotpos

end Collatz.Arctic
