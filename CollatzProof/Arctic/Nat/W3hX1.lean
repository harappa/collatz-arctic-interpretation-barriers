/-
# The word of the end point `x₁` and the counting of window frequencies (Proposition 12.28 of the paper)

The probabilistic part of Proposition 12.28 of the paper (the lower bound at the end point). The word of the end point `x₁ = c_σ + 3^A t` is split into the top part of `h := ⌊x₁/2^n⌋` (not controlled),
the low `b` digits of `h` (Lemma 6.4 (ii): within total variation distance `TV` of uniform), the top `K` digits of `ϖ` (not controlled), the middle `F` digits of `ϖ`
(Lemma 6.4 (i): exactly uniform, by a bijection in `u`) and the shared low `s'` digits; the values `u` for which the window frequencies on the two long intervals are not close to uniform
are counted.

* `lln_items`: for the window functions `phi i T` of the finitely many items, a common window length `J'`, precision `δ'` and interval length `N₀` (apply `lln_of_winClose` of
  `W3d` to each item and combine; the same procedure as in the proof of `lln_terras_famX0` of `W3a`).
* `binTail_x1_split`: `bin'(x₁) = bin'(⌊h/2^b⌋) · (the b digits of h mod 2^b) · (the top K digits of ϖ) · (the middle F digits) · r_{σ₀}`.
* `winClose_x1_low`, `winClose_x1_mid`: the window frequencies on the two intervals are transferred from the words of the parts to the word of `x₁`.
* `card_bad_mid`: at most `η 2^F` values `u` have middle window frequencies that are not close (`fam_mid_bijOn`, `win_bad_count`).
* `card_bad_low`: at most `(η + TV) 2^F` values `u` have window frequencies of the low digits of `h` that are not close (`fam_end_tv`).
-/
import CollatzProof.Arctic.Nat.W3hGroup
import CollatzProof.Arctic.CoreU

namespace Collatz.Arctic.NatQ5.W3h

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W3c
open Collatz.Arctic.MinIdeal (BRel)

set_option linter.unusedSectionVars false

/-! ## §1 Constants of the law of large numbers common to the window functions of the items -/

namespace Setup

variable {Q : Type} [Fintype Q] [DecidableEq Q] {B : ValAuto Q} (S : Setup B)

/-- **Constants of the law of large numbers common to the items**: for the window functions `phi i T` with truncation `T` (all items `i`) there are a common window length `J'`, precision
`δ' > 0` and interval length `N₀` such that, if the window frequencies on an interval `[a, b)` (`b - a ≥ N₀`) are within `δ'`, then, reading from any state of the class,
`|wsum - Q_T(i) (k - a)| ≤ ε (b - a)` for all `k ∈ [a, b]`. -/
theorem lln_items (T : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ J' : ℕ, ∃ δ' : ℚ, 0 < δ' ∧ ∃ N₀ : ℕ, ∀ (ω : List Bool) (a b : ℕ),
      WinClose (ω.map W3d.ofB) a b J' δ' → N₀ ≤ b - a → ∀ i : S.Item, ∀ x, Dfa.Reach (muStepB B) S.e x →
        ∀ k, a ≤ k → k ≤ b →
          |W3d.wsum (muStepB B) T (S.phi i T) x (ω.drop a) (k - a) - S.QJ i T * ((k - a : ℕ) : ℝ)| ≤
            ε * ((b - a : ℕ) : ℝ) := by
  have hlln := fun i : S.Item => W3d.lln_of_winClose T S.e_recurrent (S.abs_phi_le i T) ε hε
  choose J₀ δ' hδ' hJ using hlln
  set J' := Finset.univ.sup J₀
  obtain ⟨δ'', hδ''0, hδ''le⟩ := W3a.exists_pos_le_all δ' hδ'
  have hN := fun i => hJ i J' (Finset.le_sup (f := J₀) (Finset.mem_univ i))
  choose N₀ hN₀ using hN
  refine ⟨J', δ'', hδ''0, Finset.univ.sup N₀, fun ω a b hw hab i x hx k hk1 hk2 => ?_⟩
  have hNi : N₀ i ≤ Finset.univ.sup N₀ := Finset.le_sup (f := N₀) (Finset.mem_univ i)
  exact hN₀ i ω a b (W3d.winClose_mono hw (hδ''le i)) (le_trans hNi hab) x hx k hk1 hk2

end Setup

/-! ## §2 The word of the end point -/

section X1

variable {β₀ β : List Bool} {n K τ u : ℕ}

/-- **Splitting the word of the end point**: if `2^b ≤ h`, then `bin'(x₁) = bin'(⌊h/2^b⌋) · (h mod 2^b) · (the top of ϖ) · (the middle) · r_{σ₀}`. -/
theorem binTail_x1_split (b : ℕ) (hK : 1 ≤ K) (hKn : K + (parityOf β₀).length ≤ n) (hτ1 : 2 ^ (K - 1) ≤ τ)
    (hA : 1 ≤ terrasA (parityOf β)) (hb : 2 ^ b ≤ famX1 β₀ β n K τ u / 2 ^ n) :
    binTail (famX1 β₀ β n K τ u) = binTail (famX1 β₀ β n K τ u / 2 ^ n / 2 ^ b)
      ++ bitsMSB b (famX1 β₀ β n K τ u / 2 ^ n % 2 ^ b)
      ++ bitsMSB K (famX1 β₀ β n K τ u % 2 ^ n / 2 ^ (n - K))
      ++ bitsMSB (n - K - (parityOf β₀).length)
          (famX1 β₀ β n K τ u % 2 ^ n % 2 ^ (n - K) / 2 ^ (parityOf β₀).length)
      ++ bitsMSB (parityOf β₀).length (terrasR (parityOf β₀)) := by
  rw [W3a.binTail_famX1_split hK hKn hτ1 hA, fam_binTail_divmod _ b hb]

/-- Transferring the window frequencies of an interval (the interval of the low `b` digits). -/
theorem winClose_x1_low {b J : ℕ} {δ : ℚ} (hK : 1 ≤ K) (hKn : K + (parityOf β₀).length ≤ n)
    (hτ1 : 2 ^ (K - 1) ≤ τ) (hA : 1 ≤ terrasA (parityOf β)) (hb : 2 ^ b ≤ famX1 β₀ β n K τ u / 2 ^ n)
    (h : WinClose (bitsMSB b (famX1 β₀ β n K τ u / 2 ^ n % 2 ^ b)) 0 b J δ) :
    WinClose (binTail (famX1 β₀ β n K τ u)) (lenT (famX1 β₀ β n K τ u / 2 ^ n / 2 ^ b))
      (lenT (famX1 β₀ β n K τ u / 2 ^ n / 2 ^ b) + b) J δ := by
  rw [binTail_x1_split b hK hKn hτ1 hA hb]
  have h1 := W3d.winClose_append_left (binTail (famX1 β₀ β n K τ u / 2 ^ n / 2 ^ b)) h
  rw [add_zero] at h1
  have h2 := W3d.winClose_append_right (bitsMSB K (famX1 β₀ β n K τ u % 2 ^ n / 2 ^ (n - K))
      ++ bitsMSB (n - K - (parityOf β₀).length)
          (famX1 β₀ β n K τ u % 2 ^ n % 2 ^ (n - K) / 2 ^ (parityOf β₀).length)
      ++ bitsMSB (parityOf β₀).length (terrasR (parityOf β₀))) h1
  simpa only [List.append_assoc, lenT] using h2

/-- Transferring the window frequencies of an interval (the middle interval). -/
theorem winClose_x1_mid {b J : ℕ} {δ : ℚ} (hK : 1 ≤ K) (hKn : K + (parityOf β₀).length ≤ n)
    (hτ1 : 2 ^ (K - 1) ≤ τ) (hA : 1 ≤ terrasA (parityOf β)) (hb : 2 ^ b ≤ famX1 β₀ β n K τ u / 2 ^ n)
    (h : WinClose (bitsMSB (n - K - (parityOf β₀).length)
      (famX1 β₀ β n K τ u % 2 ^ n % 2 ^ (n - K) / 2 ^ (parityOf β₀).length)) 0 (n - K - (parityOf β₀).length) J δ) :
    WinClose (binTail (famX1 β₀ β n K τ u)) (lenT (famX1 β₀ β n K τ u / 2 ^ n / 2 ^ b) + b + K)
      (lenT (famX1 β₀ β n K τ u / 2 ^ n / 2 ^ b) + b + K + (n - K - (parityOf β₀).length)) J δ := by
  rw [binTail_x1_split b hK hKn hτ1 hA hb]
  have h1 := W3d.winClose_append_left (binTail (famX1 β₀ β n K τ u / 2 ^ n / 2 ^ b)
      ++ bitsMSB b (famX1 β₀ β n K τ u / 2 ^ n % 2 ^ b)
      ++ bitsMSB K (famX1 β₀ β n K τ u % 2 ^ n / 2 ^ (n - K))) h
  have hl : (binTail (famX1 β₀ β n K τ u / 2 ^ n / 2 ^ b)
      ++ bitsMSB b (famX1 β₀ β n K τ u / 2 ^ n % 2 ^ b)
      ++ bitsMSB K (famX1 β₀ β n K τ u % 2 ^ n / 2 ^ (n - K))).length =
      lenT (famX1 β₀ β n K τ u / 2 ^ n / 2 ^ b) + b + K := by
    simp only [List.length_append, bitsMSB_length]; rfl
  rw [hl, add_zero] at h1
  have h2 := W3d.winClose_append_right (bitsMSB (parityOf β₀).length (terrasR (parityOf β₀))) h1
  simpa only [List.append_assoc] using h2

open Classical in
/-- **Counting the middle windows** (Lemma 6.4 (i) of the paper, bijection). -/
theorem card_bad_mid (J : ℕ) (δ η : ℚ) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ M₀ : ℕ, ∀ (β₀ β : List Bool) (n K τ : ℕ), K + (parityOf β₀).length ≤ n →
      M₀ ≤ n - K - (parityOf β₀).length →
      (((Finset.range (2 ^ (n - K - (parityOf β₀).length))).filter (fun u =>
          ¬ WinClose (bitsMSB (n - K - (parityOf β₀).length)
            (famX1 β₀ β n K τ u % 2 ^ n % 2 ^ (n - K) / 2 ^ (parityOf β₀).length)) 0
              (n - K - (parityOf β₀).length) J δ)).card : ℚ) ≤
        η * 2 ^ (n - K - (parityOf β₀).length) := by
  obtain ⟨M₀, hM₀⟩ := win_bad_count J δ η hδ hη
  refine ⟨M₀, fun β₀ β n K τ hKn hM => ?_⟩
  set F := n - K - (parityOf β₀).length
  set mid := fun u => famX1 β₀ β n K τ u % 2 ^ n % 2 ^ (n - K) / 2 ^ (parityOf β₀).length
  have hbij := fam_mid_bijOn β₀ β τ hKn
  have hcard : ((Finset.range (2 ^ F)).filter (fun u => ¬ WinClose (bitsMSB F (mid u)) 0 F J δ)).card =
      ((Finset.range (2 ^ F)).filter (fun v => ¬ WinClose (bitsMSB F v) 0 F J δ)).card := by
    refine Finset.card_bij (fun u _ => mid u) (fun u hu => ?_) (fun u₁ hu₁ u₂ hu₂ h => ?_) (fun v hv => ?_)
    · rw [Finset.mem_filter] at hu ⊢
      exact ⟨by simpa using hbij.mapsTo (by simpa using hu.1), hu.2⟩
    · exact hbij.injOn (by simpa using (Finset.mem_filter.mp hu₁).1) (by simpa using (Finset.mem_filter.mp hu₂).1) h
    · rw [Finset.mem_filter] at hv
      obtain ⟨u, hu, hmu⟩ := hbij.surjOn (by simpa using hv.1)
      have hmu' : mid u = v := hmu
      exact ⟨u, Finset.mem_filter.mpr ⟨by simpa using hu, by rw [hmu']; exact hv.2⟩, hmu⟩
  rw [hcard]
  exact hM₀ F 0 F (Nat.zero_le _) le_rfl (by omega)

open Classical in
/-- **Counting the low windows** (Lemma 6.4 (ii) of the paper, total variation distance). -/
theorem card_bad_low (J : ℕ) (δ η : ℚ) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ M₀ : ℕ, ∀ (β₀ β : List Bool) (n K τ b Δ : ℕ), K + (parityOf β₀).length ≤ n → M₀ ≤ b →
      2 ^ (b + Δ + K) ≤ 3 ^ terrasA (parityOf β) →
      (((Finset.range (2 ^ (n - K - (parityOf β₀).length))).filter (fun u =>
          ¬ WinClose (bitsMSB b (famX1 β₀ β n K τ u / 2 ^ n % 2 ^ b)) 0 b J δ)).card : ℚ) ≤
        (η + (3 / 2 ^ Δ + 2 ^ ((parityOf β₀).length + 2) * (3 ^ terrasA (parityOf β) : ℕ) / 2 ^ n)) *
          2 ^ (n - K - (parityOf β₀).length) := by
  obtain ⟨M₀, hM₀⟩ := win_bad_count J δ η hδ hη
  refine ⟨M₀, fun β₀ β n K τ b Δ hKn hM hb => ?_⟩
  set F := n - K - (parityOf β₀).length
  set lo := fun u => famX1 β₀ β n K τ u / 2 ^ n % 2 ^ b
  set bad := (Finset.range (2 ^ b)).filter (fun j => ¬ WinClose (bitsMSB b j) 0 b J δ)
  have hTV := fam_end_tv β₀ β τ b Δ hKn hb
  have hbad : (bad.card : ℚ) ≤ η * 2 ^ b := hM₀ b 0 b (Nat.zero_le _) le_rfl (by omega)
  -- split into fibres
  have hfib : ((Finset.range (2 ^ F)).filter (fun u => ¬ WinClose (bitsMSB b (lo u)) 0 b J δ)).card =
      ∑ j ∈ bad, ((Finset.range (2 ^ F)).filter (fun u => lo u = j)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := lo) (t := bad)]
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      congr 1
      ext u
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        refine ⟨⟨h1, ?_⟩, h3⟩
        rw [h3]; exact (Finset.mem_filter.mp hj).2
    · intro u hu
      rw [Finset.mem_coe, Finset.mem_filter] at hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by positivity)), hu.2⟩
  have hF : (0 : ℚ) < 2 ^ F := by positivity
  have hfiber : ∀ j ∈ bad, (((Finset.range (2 ^ F)).filter (fun u => lo u = j)).card : ℚ) ≤
      2 ^ F * (1 / 2 ^ b + |(((Finset.range (2 ^ F)).filter (fun u => lo u = j)).card : ℚ) / 2 ^ F - 1 / 2 ^ b|) := by
    intro j _
    set c : ℚ := (((Finset.range (2 ^ F)).filter (fun u => lo u = j)).card : ℚ)
    have := le_abs_self (c / 2 ^ F - 1 / 2 ^ b)
    calc c = 2 ^ F * (c / 2 ^ F) := by field_simp
      _ ≤ 2 ^ F * (1 / 2 ^ b + |c / 2 ^ F - 1 / 2 ^ b|) :=
        mul_le_mul_of_nonneg_left (by linarith) hF.le
  rw [hfib, Nat.cast_sum]
  calc ∑ j ∈ bad, (((Finset.range (2 ^ F)).filter (fun u => lo u = j)).card : ℚ)
      ≤ ∑ j ∈ bad, 2 ^ F * (1 / 2 ^ b + |(((Finset.range (2 ^ F)).filter (fun u => lo u = j)).card : ℚ) / 2 ^ F -
          1 / 2 ^ b|) := Finset.sum_le_sum hfiber
    _ = 2 ^ F * (bad.card / 2 ^ b + ∑ j ∈ bad, |(((Finset.range (2 ^ F)).filter (fun u => lo u = j)).card : ℚ) /
          2 ^ F - 1 / 2 ^ b|) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ 2 ^ F * (η + (3 / 2 ^ Δ + 2 ^ ((parityOf β₀).length + 2) * (3 ^ terrasA (parityOf β) : ℕ) / 2 ^ n)) := by
        apply mul_le_mul_of_nonneg_left _ hF.le
        have h1 : (bad.card : ℚ) / 2 ^ b ≤ η := by rw [div_le_iff₀ (by positivity)]; exact hbad
        have h2 : ∑ j ∈ bad, |(((Finset.range (2 ^ F)).filter (fun u => lo u = j)).card : ℚ) / 2 ^ F - 1 / 2 ^ b| ≤
            ∑ j ∈ Finset.range (2 ^ b), |(((Finset.range (2 ^ F)).filter (fun u => lo u = j)).card : ℚ) / 2 ^ F -
              1 / 2 ^ b| :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => abs_nonneg _)
        have h3 := hTV
        simp only [lo] at h2
        linarith
    _ = _ := by ring

end X1

end Collatz.Arctic.NatQ5.W3h
