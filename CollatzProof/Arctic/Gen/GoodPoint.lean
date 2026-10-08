/-
Generic layer: existence of a good point on the point family.

Adapted from `CoreGoodPoint.lean` for $T$ (the proof of Theorem 6.8: intersect the events on `σ` and on `t`, and take a point
satisfying the upper bound at the starting point, the lower bound at the end point, the expansion and the number of uses at the same time).

Changes from the source:
* The number of uses is the event for **a single rule `ρ`** (`HUseR`, item (2) of `Gen.sigma_good`). The source treated the two dynamic rules and the three
  left-end rules at the same time with the constant `min(3, c_L)`; here `c_U := c_L`.
* The length of the returned orbit is the **number of steps** `BM.steps βf` (`f^[·]`, `usesOrbitG`, the domain condition). The `m` in `2^m`, `bitsMSB`,
  `blockEnd` and in the length estimates is the **number of bits** `(parityOf βf).length`.
-/
import CollatzProof.Arctic.Gen.Point
import CollatzProof.Arctic.Gen.Sigma
import CollatzProof.Arctic.CoreGood
import CollatzProof.Arctic.CoreArith

namespace Collatz.Arctic.Gen

open Collatz.Arctic MinIdeal Matrix Classical

variable {D : ℕ}

/-- **Existence of a good point** (the form for a single rule `ρ`; the length of the orbit is the number of steps). -/
theorem good_point (BM : BlockModel) (cd : ℕ → List Rule) (ρ : Rule) (hSP : HSP)
    (hTW : HTerrasWinR BM.R) (hU : HUseR BM.f BM.R BM.steps cd ρ)
    (A : Interp D) (u₀ c : Fin D → Arc) {K₀ : Set (BRel (Fin D))}
    (hK : IsMinIdeal (Mon (B0 A) (B1 A)) K₀) {E : BRel (Fin D)} (hEK : E ∈ K₀) (hE : E * E = E)
    (us : Word) (hus : IsDigits us) (hEus : suppRel (ev A us) = E)
    (wstar : List Bool)
    (hw : ∀ q₀, Dfa.Recurrent (supDelta A) q₀ → ∀ (i : ZMod (Dfa.period (supDelta A) q₀))
      (v : List Bool), Dfa.img (supDelta A) (v ++ wstar) (Dfa.classSet (supDelta A) q₀ i) =
        Dfa.img (supDelta A) wstar (Dfa.classSet (supDelta A) q₀ (i + v.length)))
    (w₀ : List Bool) (hw₀ : ∀ q, Dfa.Recurrent (supDelta A) (Dfa.run (supDelta A) q w₀)) (hw₀ne : w₀ ≠ [])
    (β₀ : List Bool) (S₁ z : Word) (hS₁ : IsDigits S₁)
    (hS : bitsMSB (parityOf β₀).length (BM.R β₀) = S₁ ++ wstar.map ofBool ++ us ++ z)
    (wlo : List Bool) (Xlo : Finset (Fin D)) (hrun : Dfa.run (supDelta A) (suppF u₀) wlo = Xlo)
    (hrec : Dfa.Recurrent (supDelta A) Xlo) (αlo : ℝ)
    (hαlo : alphaZ hE A c z (cfgOf A hE (S₁ ++ wstar.map ofBool) Xlo) = αlo)
    (hmin : ∀ X, Dfa.Reach (supDelta A) (suppF u₀) X → Dfa.Recurrent (supDelta A) X →
      αlo ≤ alphaZ hE A c z (cfgOf A hE (S₁ ++ wstar.map ofBool) X)) :
    ∃ C₁ Cst cU ce : ℝ, 0 ≤ C₁ ∧ 0 ≤ Cst ∧ 0 < cU ∧ 0 < ce ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 16 → ∃ Cε : ℝ, ∀ N : ℕ,
      ∃ x0 m k : ℕ, N ≤ k ∧ N ≤ x0 ∧ (∀ i < m, BM.dom (BM.f^[i] x0)) ∧
        (∀ V : ℕ, autoVal u₀ A c x0 = Arc.fin V → (V : ℝ) ≤ (αlo + C₁ * ε) * lenT x0 + Cε) ∧
        (∀ V : ℕ, autoVal u₀ A c (BM.f^[m] x0) = Arc.fin V →
          (αlo - ε) * lenT (BM.f^[m] x0) - Cst ≤ V) ∧
        (lenT x0 : ℝ) + ce * k ≤ lenT (BM.f^[m] x0) ∧
        (lenT (BM.f^[m] x0) : ℝ) ≤ 50 * k + Cε ∧
        cU * k ≤ usesOrbitG BM.f cd ρ x0 m := by
  -- constants determined by the automaton
  have hαnn : 0 ≤ αlo := hαlo ▸ alphaZ_nonneg hE A c z _
  obtain ⟨C₁, hC₁, hup⟩ := upper_value A u₀ c hK hEK hE us hus hEus
  obtain ⟨L, hL⟩ := cfg_count A u₀ hE wstar hw hrec
  have hy : IsDigits (S₁ ++ wstar.map ofBool ++ us) :=
    isDigits_append (isDigits_append hS₁ (isDigits_ofBool wstar)) hus
  have hyu : us <:+ S₁ ++ wstar.map ofBool ++ us := List.suffix_append _ _
  obtain ⟨Cst, hlowc⟩ := low_count (BM := BM) hSP A u₀ hK hEK hE us hus hEus
    (S₁ ++ wstar.map ofBool ++ us) z hy hyu (wlo.length + 1 + (L + 6))
  obtain ⟨cL, hcL, ce, hce, hsig⟩ := sigma_good BM cd ρ hTW hU β₀
  refine ⟨C₁, max Cst 0, (cL : ℝ), (ce : ℝ), hC₁, le_max_right _ _,
    by exact_mod_cast hcL, by exact_mod_cast hce, ?_⟩
  intro ε hε hε16
  -- quantities determined by `ε`
  obtain ⟨J, δ, hδ, hupε⟩ := hup ε hε
  obtain ⟨Cu, hupz⟩ := hupε z
  set M := ⌈4 / ε⌉₊ with hMdef
  have hM : 1 ≤ M := ceil_four_div_pos hε
  set η : ℝ := 1 / 2 ^ L / 8 with hη
  have hηpos : 0 < η := by positivity
  set ε' := min ε η with hε'
  have hε'pos : 0 < ε' := lt_min hε hηpos
  obtain ⟨L₀, hL₀⟩ := hlowc ε' hε'pos
  set εwq : ℚ := 1 / 2 ^ L / (8 * M) with hεwq
  have hεwqpos : 0 < εwq := by positivity
  obtain ⟨M₀, hM₀⟩ := win_bad_count J δ εwq hδ hεwqpos
  set εaq : ℚ := 1 / 2 ^ L / 8 with hεaq
  have hεaqpos : 0 < εaq := by positivity
  have hw₀L : w₀.map ofBool ≠ [] := by simpa using hw₀ne
  obtain ⟨D₀, hD₀⟩ := noOcc_count (isDigits_ofBool w₀) hw₀L εaq hεaqpos
  set P := Dfa.period (supDelta A) Xlo with hPdef
  have hP : 0 < P := Dfa.period_pos (supDelta A) Xlo
  set s := (parityOf β₀).length with hs
  set b₀ := β₀.length with hb₀
  set Kτ := wlo.length + 1 with hKτ
  set τ := 2 ^ wlo.length + valMSB (wlo.map ofBool) with hτ
  set R := L + 6 with hR
  refine ⟨max Cu 0 + 44 * b₀ + s + R + P + 50, fun N => ?_⟩
  -- lower bound for `k`
  set Kbig := L + Kτ + M * (M₀ + 2) + D₀ + L₀ + (L + 6) + s + Kτ + R +
    ⌈((Kτ : ℝ) + s + 12) / (2 * ε)⌉₊ + 1 with hKbig
  obtain ⟨k, hNk, β, hβk, hwinR, huse, hexp⟩ := hsig J δ hδ M hM (N + Kbig)
  set βf := β₀ ++ β with hβf
  have hpre : β₀ <+: βf := List.prefix_append _ _
  -- `m` is the number of bits (the number of steps is `BM.steps βf`)
  set m := (parityOf βf).length with hm
  set A₃ := terrasA (parityOf βf) with hA₃
  obtain ⟨hm8, hm11⟩ := parityOf_length_bounds βf
  have hβflen : βf.length = b₀ + k := by simp [hβf, hβk, hb₀]
  have hsm : s ≤ m := fam_s_le hpre
  have hA5 : 5 * βf.length ≤ A₃ := fam_terrasA_ge βf
  have hkK : Kbig ≤ k := by omega
  -- choice of `n`: `n = 2m + s + R + j`, `F + m ≡ 0 (mod P)`
  obtain ⟨hjmod, hjlt⟩ := period_align P (3 * m + R - Kτ) hP
  set j := (P - (3 * m + R - Kτ) % P) % P with hj
  set n := 2 * m + s + R + j with hn
  set F := n - Kτ - s with hF
  have hKm : Kτ ≤ m := by omega
  have hFeq : F = 2 * m + R + j - Kτ := by omega
  have hKn : Kτ + s ≤ n := by omega
  have hFm : F + m = (3 * m + R - Kτ) + j := by omega
  have hper : ((F + (bitsMSB s (famRho BM β₀ βf) ++
      bitsMSB (m - s) (famRtop BM β₀ βf)).length : ℕ) : ZMod P) = 0 := by
    rw [List.length_append, bitsMSB_length, bitsMSB_length, show s + (m - s) = m by omega, hFm]
    have : NeZero P := ⟨by omega⟩
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero hjmod
  -- the number `bb` of low bits of `h`
  set lg := Nat.log 2 (3 ^ A₃) with hlg
  have hlg1 : 2 ^ lg ≤ 3 ^ A₃ := Nat.pow_log_le_self 2 (by positivity)
  have hlg2 : 3 ^ A₃ < 2 ^ (lg + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hlgA : A₃ ≤ lg := Nat.le_log_of_pow_le (by norm_num)
    (le_trans (Nat.pow_le_pow_left (by norm_num) A₃) le_rfl)
  set bb := lg - Kτ - (L + 6) with hbb
  have hbbK : bb + (L + 6) + Kτ = lg := by omega
  have hb1 : 2 ^ (bb + (L + 6) + Kτ) ≤ 3 ^ A₃ := by rw [hbbK]; exact hlg1
  have hb2 : 3 ^ A₃ < 2 ^ (bb + (Kτ + (L + 6) + 1)) := by
    rw [show bb + (Kτ + (L + 6) + 1) = lg + 1 by omega]; exact hlg2
  have hτb := tau_bounds wlo
  have hτ1 : 2 ^ (Kτ - 1) ≤ τ := hτb.1
  have hτ2 : τ < 2 ^ Kτ := hτb.2
  have hτpos : 1 ≤ τ := le_trans Nat.one_le_two_pow hτ1
  have hbinτ : binTail τ = wlo.map ofBool := binTail_tau wlo
  -- facts for large `k`
  have hFL : L ≤ F := by omega
  have hFM : M * (M₀ + 2) ≤ F := by omega
  have hFD : D₀ ≤ F := by omega
  have hFL₀ : L₀ ≤ F := by omega
  have hbbL₀ : L₀ ≤ bb := by omega
  -- event (c): the configuration at the starting point
  set v := bitsMSB s (famRho BM β₀ βf) ++ bitsMSB (m - s) (famRtop BM β₀ βf) with hv
  have hvdig : IsDigits v := isDigits_append (bitsMSB_isDigits _ _) (bitsMSB_isDigits _ _)
  have hrunτ : Dfa.run (supDelta A) (suppF u₀) ((binTail τ).map toBool) = Xlo := by
    rw [hbinτ, map_toBool_ofBool, hrun]
  have h1n := hL (binTail τ) S₁ v F (isDigits_binTail τ) hS₁ hvdig hrunτ hFL hper
  have h1 : (2 : ℝ) ^ (F - L) ≤ (((Finset.range (2 ^ F)).filter (fun x =>
      cfgOf A hE (S₁ ++ wstar.map ofBool) (suppF (vecAfter u₀ A (binTail τ ++ bitsMSB F x ++ v))) =
        cfgOf A hE (S₁ ++ wstar.map ofBool) Xlo)).card : ℝ) := by exact_mod_cast h1n
  -- event (d): windows of the free bits
  have h2 : ∀ t < M, (((Finset.range (2 ^ F)).filter (fun x =>
      ¬ WinClose (bitsMSB F x) (t * F / M) ((t + 1) * F / M) J δ)).card : ℝ) ≤
        (εwq : ℝ) * 2 ^ F := by
    intro t ht
    have hab : t * F / M ≤ (t + 1) * F / M := mul_div_mono t (t + 1) F M (by omega)
    have hbF : (t + 1) * F / M ≤ F := by
      calc (t + 1) * F / M ≤ M * F / M := mul_div_mono _ _ F M (by omega)
        _ = F := Nat.mul_div_cancel_left _ (by omega)
    have hwid : M₀ ≤ (t + 1) * F / M - t * F / M := by
      have h1' : t * F / M + F / M ≤ (t * F + F) / M := Nat.div_add_div_le_add_div
      have h2' : M₀ + 2 ≤ F / M := by
        rw [Nat.le_div_iff_mul_le (by omega)]; linarith [hFM]
      rw [show t * F + F = (t + 1) * F by ring] at h1'
      omega
    have := hM₀ F (t * F / M) ((t + 1) * F / M) hab hbF hwid
    exact_mod_cast this
  -- event (d): lower bound at the end point
  have hS' : bitsMSB s (BM.R β₀) = (S₁ ++ wstar.map ofBool ++ us) ++ z := by
    rw [hS]
  have h3 := hL₀ β₀ βf n Kτ τ bb (L + 6) (by omega) hKn hτ1 hτ2 hb1 hb2 le_rfl hbbL₀ hFL₀ hS'
  set θ : ℝ := (3 : ℝ) / 2 ^ (L + 6) + 2 ^ (s + 2) * 3 ^ A₃ / 2 ^ n with hθ
  have hnat : 2 ^ (s + 2) * 3 ^ A₃ * 2 ^ (L + 6) ≤ 4 * 2 ^ n := by
    have h3A : 3 ^ A₃ ≤ 2 ^ (2 * m) := fam_three_pow_le A₃ m (fam_terrasA_le_length _)
    calc 2 ^ (s + 2) * 3 ^ A₃ * 2 ^ (L + 6) ≤ 2 ^ (s + 2) * 2 ^ (2 * m) * 2 ^ (L + 6) := by
          gcongr
      _ = 4 * 2 ^ (2 * m + s + (L + 6)) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, ← pow_add, ← pow_add]; congr 1; ring
      _ ≤ 4 * 2 ^ n := by
          have : 2 * m + s + (L + 6) ≤ n := by omega
          gcongr
  have hθle : θ ≤ 7 / 2 ^ (L + 6) := by
    have hr : (2 : ℝ) ^ (s + 2) * 3 ^ A₃ * 2 ^ (L + 6) ≤ 4 * 2 ^ n := by exact_mod_cast hnat
    have hpos1 : (0 : ℝ) < 2 ^ n := by positivity
    have hpos2 : (0 : ℝ) < 2 ^ (L + 6) := by positivity
    have : 2 ^ (s + 2) * (3 : ℝ) ^ A₃ / 2 ^ n ≤ 4 / 2 ^ (L + 6) := by
      rw [div_le_div_iff₀ hpos1 hpos2]; linarith
    have e : (3 : ℝ) / 2 ^ (L + 6) + 4 / 2 ^ (L + 6) = 7 / 2 ^ (L + 6) := by ring
    simp only [hθ]
    linarith
  -- event: the absorbing word at the end point
  set mid := fun x => famX1 BM β₀ βf n Kτ τ x % 2 ^ n % 2 ^ (n - Kτ) / 2 ^ s with hmid
  have h4 : (((Finset.range (2 ^ F)).filter (fun x => ¬ ∃ i, i + (w₀.map ofBool).length ≤ F ∧
      window (bitsMSB F (mid x)) i (w₀.map ofBool).length = w₀.map ofBool)).card : ℝ) ≤
      (εaq : ℝ) * 2 ^ F := by
    have hb := card_filter_comp_bij (2 ^ F) mid (fam_mid_bijOn β₀ βf τ hKn)
      (fun y => ∀ i, 0 ≤ i → i + (w₀.map ofBool).length ≤ F →
        window (bitsMSB F y) i (w₀.map ofBool).length ≠ w₀.map ofBool)
    have hD := hD₀ F 0 F le_rfl (by omega)
    have heq : ((Finset.range (2 ^ F)).filter (fun x => ¬ ∃ i, i + (w₀.map ofBool).length ≤ F ∧
        window (bitsMSB F (mid x)) i (w₀.map ofBool).length = w₀.map ofBool)) =
        ((Finset.range (2 ^ F)).filter (fun x => ∀ i, 0 ≤ i → i + (w₀.map ofBool).length ≤ F →
          window (bitsMSB F (mid x)) i (w₀.map ofBool).length ≠ w₀.map ofBool)) := by
      apply Finset.filter_congr
      intro x _
      constructor
      · intro h i _ hi heq; exact h ⟨i, hi, heq⟩
      · rintro h ⟨i, hi, heq⟩; exact h i (Nat.zero_le _) hi heq
    rw [heq, hb]
    exact_mod_cast hD
  -- intersection of the four events
  have hsmall : (M : ℝ) * (εwq : ℝ) + (θ / 2 + ε') + (εaq : ℝ) < 1 / 2 ^ L := by
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    have e1 : (M : ℝ) * (εwq : ℝ) = 1 / 2 ^ L / 8 := by
      rw [hεwq]; push_cast; field_simp
    have e2 : (εaq : ℝ) = 1 / 2 ^ L / 8 := by rw [hεaq]; push_cast; ring
    have e3 : ε' ≤ 1 / 2 ^ L / 8 := min_le_right _ _
    have e4 : θ / 2 ≤ 7 / 2 ^ (L + 6) / 2 := by linarith
    have e5 : (7 : ℝ) / 2 ^ (L + 6) / 2 = (7 / 128) * (1 / 2 ^ L) := by
      rw [pow_add]; field_simp; norm_num
    have hpL : (0 : ℝ) < 1 / 2 ^ L := by positivity
    rw [e1, e2]
    have e6 : (1 : ℝ) / 2 ^ L / 8 = (1 / 8) * (1 / 2 ^ L) := by ring
    rw [e6] at e3 ⊢
    linarith
  have h3' : (1 - (θ / 2 + ε')) * 2 ^ F ≤ (((Finset.range (2 ^ F)).filter (fun x =>
      Lower.LowerAt u₀ A hE us z ε' Cst (binTail (famX1 BM β₀ βf n Kτ τ x)))).card : ℝ) := by
    have : (1 - θ / 2 - ε') = (1 - (θ / 2 + ε')) := by ring
    rw [← this]; exact h3
  obtain ⟨x, hx, e1, e2, e3, e4⟩ := exists_good_x F L M _ _ _
    (fun t x => WinClose (bitsMSB F x) (t * F / M) ((t + 1) * F / M) J δ) hFL
    (εwq : ℝ) (εaq : ℝ) (θ / 2 + ε') h1 h2 h3' h4 hsmall
  -- the good point (the length of the orbit is the number of steps `BM.steps βf`)
  have hiter : BM.f^[BM.steps βf] (famX0 BM β₀ βf n Kτ τ x) = famX1 BM β₀ βf n Kτ τ x :=
    (fam_iter β₀ βf n Kτ τ x).symm
  have hA1 : 1 ≤ A₃ := by omega
  have hCu : Cu ≤ max Cu 0 := le_max_left _ _
  have hCu0 : 0 ≤ max Cu 0 := le_max_right _ _
  refine ⟨famX0 BM β₀ βf n Kτ τ x, BM.steps βf, k, by omega, ?_, fam_orbit_dom β₀ βf x hτpos,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- `N ≤ x₀`
    have h0 := fam_X0_ge (BM := BM) β₀ βf (n := n) (K := Kτ) (τ := τ) x (by omega) (by omega) hτ1
    rw [← hm] at h0
    have h00 : n + m - 1 < 2 ^ (n + m - 1) := Nat.lt_two_pow_self
    omega
  · -- upper bound at the starting point
    have hshape := binTail_X0_shape (BM := BM) hpre hKn hτpos hx S₁ (wstar.map ofBool) us z hS
    have hsplit := binTail_X0_split (BM := BM) hpre hKn hτpos hx
    rw [← hm] at hsplit
    have hlenτ : (binTail τ).length = Kτ - 1 := fam_binTail_tau_length (by omega) hτ1 hτ2
    have hmk : 8 * k ≤ m := by have h8 := hm8; rw [hβflen] at h8; omega
    have hkε : 4 * ((Kτ : ℝ) + s + 12) ≤ ε * (8 * k) := by
      have hc : ((Kτ : ℝ) + s + 12) / (2 * ε) ≤ (⌈((Kτ : ℝ) + s + 12) / (2 * ε)⌉₊ : ℝ) :=
        Nat.le_ceil _
      have hk' : (⌈((Kτ : ℝ) + s + 12) / (2 * ε)⌉₊ : ℝ) ≤ k := by exact_mod_cast (by omega :
        ⌈((Kτ : ℝ) + s + 12) / (2 * ε)⌉₊ ≤ k)
      have h2ε : 0 < 2 * ε := by positivity
      have := le_trans hc hk'
      rw [div_le_iff₀ h2ε] at this
      linarith only [this]
    obtain ⟨hW, hexc, hcount⟩ := part_numeric hε hε16 Kτ s F m k hmk hkε
    have hwlen : (binTail τ ++ bitsMSB F x ++ bitsMSB s (famRho BM β₀ βf) ++
        bitsMSB m (BM.R βf)).length = (Kτ - 1) + F + s + m := by
      simp [hlenτ, bitsMSB_length]; omega
    have hP := x0_goodPartition (binTail τ) (bitsMSB F x) (bitsMSB s (famRho BM β₀ βf))
      (bitsMSB m (BM.R βf)) (K := Kτ) (F := F) (s := s) (m := m) (b₀ := b₀) (k := k)
      (M := M) (M' := M) (bE := blockEnd βf) ε J δ hlenτ (bitsMSB_length _ _) (bitsMSB_length _ _)
      (bitsMSB_length _ _) hM hM hsm (fun i i' h => blockEnd_mono βf h)
      (by rw [hβf]; exact blockEnd_append_length β₀ β)
      (by rw [← hβflen, blockEnd_full]) (blockEnd_sub_le βf) e2 hwinR
      (by rw [hwlen]; exact hW) hcount (by rw [hwlen]; exact hexc)
    rw [← hsplit] at hP
    have hcfg : alphaZ hE A c z (cfgOf A hE (S₁ ++ wstar.map ofBool) (suppF (vecAfter u₀ A
        (binTail τ ++ bitsMSB F x ++ v)))) = αlo := by rw [e1, hαlo]
    have hlen : (binTail (famX0 BM β₀ βf n Kτ τ x)).length ≤
        2 * ((binTail τ ++ bitsMSB F x ++ v) ++ (S₁ ++ wstar.map ofBool) ++ us).length := by
      rw [hshape]
      have hzs : z.length ≤ s := by
        have := congrArg List.length hS
        simp only [bitsMSB_length, List.length_append] at this
        omega
      simp only [List.length_append, bitsMSB_length]
      omega
    have hpos : 0 ≤ αlo + C₁ * ε := add_nonneg hαnn (mul_nonneg hC₁ hε.le)
    intro V hV
    have h := point_upper A u₀ c hE us ε C₁ Cu J δ z hupz (famX0 BM β₀ βf n Kτ τ x)
      (binTail τ ++ bitsMSB F x ++ v) (S₁ ++ wstar.map ofBool) hshape (isDigits_binTail _) _ hP hlen
      αlo hcfg hpos V hV
    have hb1 : (0 : ℝ) ≤ (b₀ : ℝ) := Nat.cast_nonneg _
    have hb2 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg _
    have hb3 : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg _
    have hb4 : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg _
    linarith only [h, hCu, hb1, hb2, hb3, hb4]
  · -- lower bound at the end point
    rw [hiter]
    have hshape := binTail_X1_shape (BM := BM) (β₀ := β₀) (β := βf) (n := n) (K := Kτ) (τ := τ)
      (x := x) (by omega) hKn hτ1 hA1 S₁ (wstar.map ofBool) us z hS
    have hpc : (bitsMSB (n - Kτ - s) (mid x)).length = F := bitsMSB_length _ _
    obtain ⟨i, hi, hwin⟩ := e4
    have hocc : ∃ i, i + (w₀.map ofBool).length ≤ (bitsMSB (n - Kτ - s) (mid x)).length ∧
        window (bitsMSB (n - Kτ - s) (mid x)) i (w₀.map ofBool).length = w₀.map ofBool :=
      ⟨i, by rw [hpc]; exact hi, hwin⟩
    have hlow := lowerAt_mono u₀ A hE us z ε' Cst (max Cst 0) (le_max_left _ _) _ e3
    intro V hV
    have h := point_lower A u₀ c hE us z hEus ε' (max Cst 0) hε'pos (le_max_right _ _) w₀ hw₀
      (famX1 BM β₀ βf n Kτ τ x) _ _ _ (S₁ ++ wstar.map ofBool) hshape (isDigits_binTail _)
      (bitsMSB_isDigits _ _) (bitsMSB_isDigits _ _) hocc hlow αlo hmin V hV
    have hεε : ε' ≤ ε := min_le_left _ _
    have hN : (0 : ℝ) ≤ lenT (famX1 BM β₀ βf n Kτ τ x) := Nat.cast_nonneg _
    have hmul : (αlo - ε) * lenT (famX1 BM β₀ βf n Kτ τ x) ≤
        (αlo - ε') * lenT (famX1 BM β₀ βf n Kτ τ x) :=
      mul_le_mul_of_nonneg_right (by linarith only [hεε]) hN
    exact le_trans (sub_le_sub_right hmul _) h
  · -- expansion
    rw [hiter]
    have hexp' : 2 ^ ((parityOf βf).length + ⌈(ce : ℚ) * k⌉₊) ≤ 3 ^ terrasA (parityOf βf) := hexp
    have h := fam_lenT_expand (BM := BM) β₀ βf (n := n) (K := Kτ) (τ := τ) (u := x) ⌈(ce : ℚ) * k⌉₊
      (by omega) hKn hτ1 hτ2 hx hexp'
    have hc : ((ce : ℚ) * k : ℚ) ≤ (⌈(ce : ℚ) * k⌉₊ : ℚ) := Nat.le_ceil _
    have hc' : (ce : ℝ) * k ≤ (⌈(ce : ℚ) * k⌉₊ : ℝ) := by exact_mod_cast hc
    have h' : ((lenT (famX0 BM β₀ βf n Kτ τ x) + ⌈(ce : ℚ) * k⌉₊ : ℕ) : ℝ) ≤
        lenT (famX1 BM β₀ βf n Kτ τ x) := by exact_mod_cast h
    push_cast at h'
    linarith only [h', hc']
  · -- length
    rw [hiter]
    have h := fam_lenT_X1_lt_two (BM := BM) β₀ βf (n := n) (K := Kτ) (τ := τ) (u := x) hKn hτpos
      hτ2 hx
    rw [← hm] at h
    have hm' : m ≤ 11 * (b₀ + k) := by rw [← hβflen]; exact hm11
    have h' : lenT (famX1 BM β₀ βf n Kτ τ x) ≤ 44 * k + (44 * b₀ + s + R + P) := by omega
    have h'' : (lenT (famX1 BM β₀ βf n Kτ τ x) : ℝ) ≤ 44 * k + (44 * b₀ + s + R + P) := by
      exact_mod_cast h'
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith only [h'', hk0, hCu0]
  · -- uses of the rule `ρ` (`t = famT ≥ 2^m`)
    have hT := fam_T_ge (BM := BM) (β₀ := β₀) (β := βf) (n := n) (K := Kτ) (τ := τ) x
      (by omega) (by omega) hτ1
    have hTm : 2 ^ m ≤ famT BM β₀ βf n Kτ τ x :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hT
    have h := huse (famT BM β₀ βf n Kτ τ x) hTm
    unfold famX0
    exact_mod_cast h

end Collatz.Arctic.Gen
