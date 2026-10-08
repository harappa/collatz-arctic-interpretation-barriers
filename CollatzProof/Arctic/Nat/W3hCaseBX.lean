/-
# Case B: the upper bound at the starting point and the lower bound at the end point, on the events (Propositions 12.27 and 12.28 of the paper)

In the proof of Proposition 12.31 of the paper: the upper bound at the starting point (Proposition 12.27) and the lower bound at the end point (Proposition 12.28), on the events. The events are
assumed in the form of the conclusions of the laws of large numbers for intervals, of the tail bound and of the window frequencies; the probabilities are estimated in `W3hCaseB.lean`. The size conditions are written in terms of `k` (the number of blocks)
and transferred from the lengths `N₀ ≥ 8k` and `N₁ ≥ N₀` of the point words.

* `x0_upper`: `V(x₀) ≤ (C_lo + ε) N₀^{d_lo}`.
* `x1_lower`: the configuration `c₁` of `x₁` lies in `𝔎`, and `(C_{d₁}(c₁) - ε) N₁^{d₁} ≤ V(x₁)` (`d₁ = degF c₁`).
-/
import CollatzProof.Arctic.Nat.W3hCaseBDet

namespace Collatz.Arctic.NatQ5.W3h

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W3c
open Collatz.Arctic.MinIdeal (BRel)

set_option linter.unusedSectionVars false

namespace Setup

variable {Q : Type} [Fintype Q] [DecidableEq Q] {B : ValAuto Q} (S : Setup B)

theorem degF_le (s : BRel (ZIdx B)) : S.degF s ≤ S.Dm := by
  classical
  unfold degF
  refine Finset.sup_le (fun d hd => ?_)
  have := Finset.mem_range.mp (Finset.mem_filter.mp hd).1
  simp only [id]; omega

/-- The word of the starting point has length at least `8k`. -/
theorem N0_ge (β' : List Bool) {n u : ℕ} (hKn : S.Kc + S.s' ≤ n) (hu : u < 2 ^ S.Flen n) :
    (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length = n + (parityOf (S.β₀ ++ β')).length - 1 ∧
      8 * β'.length ≤ (parityOf (S.β₀ ++ β')).length := by
  have hK1 : 1 ≤ S.Kc := by unfold Kc; omega
  refine ⟨?_, ?_⟩
  · rw [W3a.length_binWord]
    exact fam_lenT_X0 S.β₀ (S.β₀ ++ β') hK1 hKn S.T0_bounds.1 S.T0_bounds.2 hu
  · have := (parityOf_length_bounds (S.β₀ ++ β')).1
    rw [List.length_append] at this; omega

/-- **The upper bound at the starting point** (on the events). -/
theorem x0_upper (β' : List Bool) (n u J : ℕ) (hKn : S.Kc + S.s' ≤ n) (hu : u < 2 ^ S.Flen n)
    {clo : PSt B} {dlo : ℕ} {Clo ε η₀ θF εT : ℝ}
    (hconf : S.conf (S.mid0 (S.β₀ ++ β') n u) = clo)
    (hdeg : ∀ d, dlo < d → S.coef d clo.1 = 0) (hC : S.coef dlo clo.1 = Clo) (hdlo : 1 ≤ dlo)
    (hε0 : 0 < ε) (hη₀ : 0 < η₀) (hη₀1 : η₀ ≤ 1)
    (hfree : ∀ (i : S.Item) x, Dfa.Reach (muStepB B) S.e x → ∀ p, S.Kc - 1 ≤ p → p ≤ S.Kc - 1 + S.Flen n →
      |W3d.wsum (muStepB B) J (S.phi i J) x
        ((binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).map W3d.f2b |>.drop (S.Kc - 1))
        (p - (S.Kc - 1)) - S.QJ i J * ((p - (S.Kc - 1) : ℕ) : ℝ)| ≤ η₀ / 4 * (S.Flen n : ℝ))
    (hter : ∀ (i : S.Item) x, Dfa.Reach (muStepB B) S.e x →
      ∀ p, n - 1 ≤ p → p ≤ n - 1 + ((parityOf (S.β₀ ++ β')).length - S.s') →
      |W3d.wsum (muStepB B) J (S.phi i J) x
        ((binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).map W3d.f2b |>.drop (n - 1))
        (p - (n - 1)) - S.QJ i J * ((p - (n - 1) : ℕ) : ℝ)| ≤
        η₀ / 4 * (((parityOf (S.β₀ ++ β')).length - S.s' : ℕ) : ℝ))
    (htail : ∀ i : S.Item, ∑ p ∈ Finset.range (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length,
      ∑ r ∈ Finset.Ioc J (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length,
        (S.xiI i r (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)) p : ℝ) ≤
          θF * (S.Flen n + 1) + εT * β'.length)
    (hθ : θF ≤ η₀ / 8) (hεT : εT ≤ η₀ / 8)
    (hQ : ∀ i : S.Item, S.Qc i - S.QJ i J ≤ η₀ / 4)
    (hk0 : 1 ≤ β'.length)
    (hk1 : ((S.BJ J : ℝ) + S.Hb) * (S.C0 : ℝ) ≤ η₀ / 4 * β'.length)
    (hk2 : ∑ d ∈ Finset.range dlo, S.coef d clo.1 ≤ ε / 2 * β'.length)
    (hk3 : S.Ktot clo.1 * (S.Cst * (η₀ + 1 / β'.length)) ≤ ε / 2) :
    (aval B (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)) : ℝ) ≤
      (Clo + ε) * ((binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length : ℝ) ^ dlo := by
  obtain ⟨hN, h8⟩ := S.N0_ge β' hKn hu
  have hNk : β'.length ≤ (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length := by omega
  have hNF : S.Flen n + 1 ≤ (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length := by
    rw [hN]; unfold Flen; omega
  have hNr : (β'.length : ℝ) ≤ (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length := by
    exact_mod_cast hNk
  have hk0r : (1 : ℝ) ≤ β'.length := by exact_mod_cast hk0
  have hNFr : (S.Flen n : ℝ) + 1 ≤ (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length := by
    exact_mod_cast hNF
  -- the tail is at most `(η₀/4) N`
  have htail' : ∀ i : S.Item, ∑ p ∈ Finset.range (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length,
      ∑ r ∈ Finset.Ioc J (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length,
        (S.xiI i r (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)) p : ℝ) ≤
          η₀ / 4 * (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length := by
    intro i
    refine le_trans (htail i) ?_
    have h1 : θF * (S.Flen n + 1) ≤ η₀ / 8 * (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length :=
      mul_le_mul hθ hNFr (by positivity) (by positivity)
    have h2 : εT * β'.length ≤ η₀ / 8 * (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length :=
      mul_le_mul hεT hNr (by positivity) (by positivity)
    linarith
  have hC0 : ((S.Kc - 1 + 2 * S.s' : ℕ) : ℝ) = (S.C0 : ℝ) := rfl
  have hI := S.iterHyp_x0 β' n u J hKn hu (εL := η₀ / 4) (θ := η₀ / 4) (η₃ := η₀ / 4) (η := η₀)
    (by positivity) hfree hter htail' hQ (by
      rw [hC0]
      have : ((S.BJ J : ℝ) + S.Hb) * (S.C0 : ℝ) ≤
          η₀ / 4 * (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length :=
        le_trans hk1 (mul_le_mul_of_nonneg_left hNr (by positivity))
      linarith) hη₀1
  have hωf := S.binWord_x0 β' hKn hu
  generalize binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u) = ω at hNr hNk hI hωf ⊢
  subst hωf
  have hst : S.D.sT (S.mid0 (S.β₀ ++ β') n u) = clo.1 := by rw [← S.conf_fst, hconf]
  refine S.up_bound _ (by rw [hst]; exact hdeg) (by rw [hst]; exact hC) hdlo hη₀.le (by omega) hI ?_ ?_
  · rw [hst]
    exact le_trans hk2 (mul_le_mul_of_nonneg_left hNr (by linarith))
  · rw [hst]
    refine le_trans ?_ hk3
    have hK0 := S.Ktot_nonneg clo.1
    have hCs := S.Cst_pos
    have : 1 / ((fullW S.us [] S.y'' S.z (S.mid0 (S.β₀ ++ β') n u) S.R).length : ℝ) ≤ 1 / β'.length :=
      one_div_le_one_div_of_le (by linarith) hNr
    apply mul_le_mul_of_nonneg_left _ hK0
    apply mul_le_mul_of_nonneg_left _ hCs.le
    linarith

/-- **The lower bound at the end point** (on the events). -/
theorem x1_lower (β' : List Bool) (n u b M Δ k : ℕ) (hKn : S.Kc + S.s' ≤ n) (hu : u < 2 ^ S.Flen n)
    (h3 : ¬ 3 ∣ famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)
    (hA : 1 ≤ terrasA (parityOf (S.β₀ ++ β')))
    (hb1 : 2 ^ (b + Δ + S.Kc) ≤ 3 ^ terrasA (parityOf (S.β₀ ++ β')))
    (hb2 : 3 ^ terrasA (parityOf (S.β₀ ++ β')) < 2 ^ (b + (S.Kc + Δ + 1)))
    (htop : (binWord (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).take S.E = S.τ)
    {J' : ℕ} {δ' : ℚ} {N₀' : ℕ} {η₁ ε Kmax : ℝ}
    (hlln : ∀ (ω : List Bool) (a b : ℕ), WinClose (ω.map W3d.ofB) a b J' δ' → N₀' ≤ b - a →
      ∀ i : S.Item, ∀ x, Dfa.Reach (muStepB B) S.e x → ∀ k, a ≤ k → k ≤ b →
        |W3d.wsum (muStepB B) M (S.phi i M) x (ω.drop a) (k - a) - S.QJ i M * ((k - a : ℕ) : ℝ)| ≤
          η₁ / 4 * ((b - a : ℕ) : ℝ))
    (hN₀'b : N₀' ≤ b) (hN₀'F : N₀' ≤ S.Flen n)
    (hlow : WinClose (bitsMSB b (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u / 2 ^ n % 2 ^ b)) 0 b J' δ')
    (hmid : WinClose (bitsMSB (n - S.Kc - (parityOf S.β₀).length)
      (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u % 2 ^ n % 2 ^ (n - S.Kc) / 2 ^ (parityOf S.β₀).length)) 0
        (n - S.Kc - (parityOf S.β₀).length) J' δ')
    (hη₁ : 0 < η₁) (hη₁1 : η₁ ≤ 1) (hM : 1 ≤ M) (hMF : M ≤ S.Flen n)
    (hKmax : ∀ c ∈ S.Kset, S.Ktot c.1 ≤ Kmax)
    (hcoefM : ∀ c ∈ S.Kset, ∀ d ≤ S.Dm, S.coef d c.1 - ε / 3 ≤ S.coefM M d c.1)
    (hk : 1 ≤ k) (hNk : k ≤ (binWord (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length)
    (hK1 : Kmax * (S.Cst * (η₁ + 1 / k)) ≤ ε / 3)
    (hK2 : Kmax * (S.Dm * ((M - 1 : ℕ) : ℝ) * (max (S.BJ M : ℝ) 1) ^ S.Dm) ≤ ε / 3 * k)
    (hK3 : ((S.BJ M : ℝ) + S.Hb) * ((2 * S.Kc + Δ + M + S.s' : ℕ) : ℝ) ≤ η₁ / 2 * k) :
    ∃ c₁ ∈ S.Kset, (S.coef (S.degF c₁.1) c₁.1 - ε) *
        ((binWord (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length : ℝ) ^ (S.degF c₁.1) ≤
      (aval B (binWord (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)) : ℝ) := by
  have hK1' : 1 ≤ S.Kc := by unfold Kc; omega
  obtain ⟨hhb, hlenh⟩ := fam_h_low (β₀ := S.β₀) (β := S.β₀ ++ β') (n := n) (K := S.Kc) (τ := S.T0) u b Δ hK1'
    (by omega) S.T0_bounds.1 hb1
  have hb : 2 ^ b ≤ famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u / 2 ^ n :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hhb
  have hhigh := fam_h_high (β₀ := S.β₀) (β := S.β₀ ++ β') (n := n) (K := S.Kc) (τ := S.T0) (u := u) b Δ hKn
    S.T0_bounds.2 hu hb2
  have hEK : S.E ≤ lenT (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u / 2 ^ n / 2 ^ b) := by
    have : S.Kc = S.E + 9 := rfl
    omega
  obtain ⟨m₁, hω₁, hlen1, hlen2⟩ := S.binWord_x1 β' hKn hA hb hEK htop
  have hwl := winClose_x1_low (β₀ := S.β₀) (β := S.β₀ ++ β') (n := n) (K := S.Kc) (τ := S.T0) (u := u)
    hK1' hKn S.T0_bounds.1 hA hb hlow
  have hwm := winClose_x1_mid (β₀ := S.β₀) (β := S.β₀ ++ β') (n := n) (K := S.Kc) (τ := S.T0) (u := u)
    hK1' hKn S.T0_bounds.1 hA hb hmid
  rw [← W3a.map_ofB_binWord] at hwl hwm
  generalize lenT (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u / 2 ^ n / 2 ^ b) = a₁ at hwl hwm hlen1 hlen2 hhigh hEK
  have hFn : n - S.Kc - (parityOf S.β₀).length = S.Flen n := rfl
  rw [hFn] at hwm
  have hlow' := hlln _ _ _ hwl (by omega)
  have hmid' := hlln _ _ _ hwm (by omega)
  rw [Nat.add_sub_cancel_left] at hlow'
  rw [Nat.add_sub_cancel_left] at hmid'
  have hus : S.us.length ≤ a₁ := le_trans S.us_le_E hEK
  have hNr : (k : ℝ) ≤ (binWord (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length := by exact_mod_cast hNk
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hHb := S.Hb_nonneg
  have hI := S.iterHyp_x1 _ m₁ hω₁ a₁ b (S.Flen n) M hus hlen2 (ε' := η₁ / 4) (η := η₁) (by positivity)
    hlow' hmid' (by
      have hbF : (b : ℝ) + S.Flen n ≤ (binWord (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length := by
        have : b + S.Flen n ≤ (binWord (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length := by omega
        exact_mod_cast this
      have hc : ((S.BJ M : ℝ) + S.Hb) * ((a₁ + S.Kc + M + S.s' : ℕ) : ℝ) ≤
          ((S.BJ M : ℝ) + S.Hb) * ((2 * S.Kc + Δ + M + S.s' : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast (show a₁ + S.Kc + M + S.s' ≤ 2 * S.Kc + Δ + M + S.s' by omega))
          (by positivity)
      have h2 : η₁ / 2 * (k : ℝ) ≤ η₁ / 2 * (binWord (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length :=
        mul_le_mul_of_nonneg_left hNr (by positivity)
      nlinarith) hη₁1
  -- the point is not divisible by 3
  have hx1 : 1 ≤ famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u := by
    rcases Nat.eq_zero_or_pos (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u) with h0 | h0
    · exact absurd (h0 ▸ dvd_zero 3) h3
    · exact h0
  have hval := valW_binWord _ hx1
  generalize binWord (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u) = ω₁ at hI hω₁ hNr hval ⊢
  subst hω₁
  have hc₁ : S.conf m₁ ∈ S.Kset := S.conf_mem m₁ (by rw [hval]; exact h3)
  have hst : S.D.sT m₁ = (S.conf m₁).1 := (S.conf_fst m₁).symm
  refine ⟨S.conf m₁, hc₁, ?_⟩
  have hN1 : 1 ≤ (fullW S.us [] S.y'' S.z m₁ S.R).length := by
    have : (1 : ℝ) ≤ (fullW S.us [] S.y'' S.z m₁ S.R).length := le_trans hkr hNr
    exact_mod_cast this
  have hK0 := S.Ktot_nonneg (S.conf m₁).1
  have hKm := hKmax _ hc₁
  have hCs := S.Cst_pos
  have hlb := S.low_bound m₁ (S.degF (S.conf m₁).1) M hM hη₁.le hN1 (S.GoodX1 a₁ b (S.Flen n) M)
    (S.goodX1_mem m₁ (show S.τ.length ≤ a₁ from hEK) hlen1 hMF) hI (S.degF_le _)
    (by rw [hst]; exact hcoefM _ hc₁ _ (S.degF_le _))
    (by
      rw [hst]
      have : 1 / ((fullW S.us [] S.y'' S.z m₁ S.R).length : ℝ) ≤ 1 / k := one_div_le_one_div_of_le (by linarith) hNr
      have h1 : S.Cst * (η₁ + 1 / ((fullW S.us [] S.y'' S.z m₁ S.R).length : ℝ)) ≤ S.Cst * (η₁ + 1 / k) :=
        mul_le_mul_of_nonneg_left (by linarith) hCs.le
      calc S.Ktot (S.conf m₁).1 * (S.Cst * (η₁ + 1 / ((fullW S.us [] S.y'' S.z m₁ S.R).length : ℝ)))
          ≤ Kmax * (S.Cst * (η₁ + 1 / k)) := mul_le_mul hKm h1 (by positivity) (le_trans hK0 hKm)
        _ ≤ ε / 3 := hK1)
    (by
      rw [hst]
      have hX : (0 : ℝ) ≤ S.Dm * ((M - 1 : ℕ) : ℝ) * (max (S.BJ M : ℝ) 1) ^ S.Dm := by positivity
      calc S.Ktot (S.conf m₁).1 * (S.Dm * ((M - 1 : ℕ) : ℝ) * (max (S.BJ M : ℝ) 1) ^ S.Dm)
          ≤ Kmax * (S.Dm * ((M - 1 : ℕ) : ℝ) * (max (S.BJ M : ℝ) 1) ^ S.Dm) := mul_le_mul_of_nonneg_right hKm hX
        _ ≤ ε / 3 * k := hK2
        _ ≤ ε / 3 * (fullW S.us [] S.y'' S.z m₁ S.R).length := by
            have : 0 ≤ ε / 3 * k := le_trans (mul_nonneg (le_trans hK0 hKm) hX) hK2
            have hε3 : 0 ≤ ε / 3 := by
              by_contra hneg; push Not at hneg
              have : ε / 3 * (k : ℝ) < 0 := mul_neg_of_neg_of_pos hneg (by linarith)
              linarith
            exact mul_le_mul_of_nonneg_left hNr hε3)
  rw [hst] at hlb
  exact hlb

end Setup

end Collatz.Arctic.NatQ5.W3h
