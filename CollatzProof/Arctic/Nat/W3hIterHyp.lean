/-
# The hypothesis (IH) of Lemma 12.15 on point words (Propositions 12.27 (ii) and 12.28 (ii) of the paper)

The deterministic form of the step of the proofs of Propositions 12.27 and 12.28 that splits the positions into intervals on each of which the prefix sums agree. At the starting point `x₀`
(two intervals, the free bits and the Terras part, and a tail) and at the end point `x₁` (two intervals, the low part of `h` and the middle digits `ϖ`), `W3a.IterHyp`
is derived from the conclusions of the laws of large numbers on intervals.

* `iterHyp_of_parts`: if the prefix sums of the truncated sequence `g` are close to `Q_J n`, the sum of `0 ≤ ξ - g` (the tail) is small, and `Q - Q_J` is small, then
  `ξ` satisfies `IterHyp (Hb + 1) η N ξ Q`.
* `iterHyp_x0`: for `Ξ⁺` (`p ≥ |u♯|`) of the word of the starting point (the intervals `[K-1, K-1+F)` and `[n-1, n-1+m-s')`).
* `iterHyp_x1`: for `Ξ^{(M)}` restricted to the good positions of the word of the end point (the intervals `[a₁, a₁ + b)` and `[a₂, a₂ + F - M)`).
-/
import CollatzProof.Arctic.Nat.W3hPick

namespace Collatz.Arctic.NatQ5.W3h

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W3c
open Collatz.Arctic.MinIdeal (BRel)

set_option linter.unusedSectionVars false

namespace Setup

variable {Q : Type} [Fintype Q] [DecidableEq Q] {B : ValAuto Q} (S : Setup B)

theorem us_le_E : S.us.length ≤ S.E := by
  rw [E, tau_length]; exact Nat.le_mul_of_pos_left _ S.hR1

theorem us_le_Kc : S.us.length ≤ S.Kc - 1 := by
  have := S.us_le_E; unfold Kc; omega

theorem XiJ_le_BJ (i : S.Item) (J : ℕ) (ω : List (Fin 2)) (p : ℕ) : S.XiJ i J ω p ≤ S.BJ J := by
  rw [← S.phiN_eq_XiJ]; exact S.phiN_le i J _ _

/-- From the window sum of an interval (`wsum`, Definition 12.12) to the sum over the positions of the interval. -/
theorem sum_Ico_XiJ (i : S.Item) (J : ℕ) (ω : List (Fin 2)) {a q : ℕ} (_haq : a ≤ q) :
    ∑ p ∈ Finset.Ico a q, (S.XiJ i J ω p : ℝ) =
      W3d.wsum (muStepB B) J (S.phi i J) (muZ B (ω.take a)) ((ω.map W3d.f2b).drop a) (q - a) := by
  rw [S.wsum_phi, Finset.sum_Ico_eq_sum_range]

/-- **Assembling `IterHyp`**. -/
theorem iterHyp_of_parts (i : S.Item) (J N : ℕ) (ξ g : ℕ → ℝ) {E T η₃ η : ℝ}
    (hg0 : ∀ p, 0 ≤ g p) (hgξ : ∀ p, g p ≤ ξ p)
    (hpre : ∀ n ≤ N, |∑ p ∈ Finset.range n, g p - S.QJ i J * n| ≤ E)
    (htail : ∑ p ∈ Finset.range N, (ξ p - g p) ≤ T)
    (hQ : S.Qc i - S.QJ i J ≤ η₃) (hη : E + T + η₃ * N ≤ η * N) (hη1 : η ≤ 1) :
    W3a.IterHyp (S.Hb + 1) η N ξ (S.Qc i) := by
  have hQ0 := S.Qc_nonneg i
  have hQH := S.Qc_le_Hb i
  have hQJ := S.QJ_le_Qc i J
  have hη₃ : 0 ≤ η₃ := le_trans (by linarith) hQ
  have hdiff : ∀ n ≤ N, 0 ≤ ∑ p ∈ Finset.range n, (ξ p - g p) ∧
      ∑ p ∈ Finset.range n, (ξ p - g p) ≤ T := by
    intro n hn
    have h0 : ∀ p, 0 ≤ ξ p - g p := fun p => by linarith [hgξ p]
    refine ⟨Finset.sum_nonneg fun p _ => h0 p, le_trans ?_ htail⟩
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hn) (fun p _ _ => h0 p)
  have hmain : ∀ n ≤ N, |∑ p ∈ Finset.range n, ξ p - S.Qc i * n| ≤ η * N := by
    intro n hn
    have e : ∑ p ∈ Finset.range n, ξ p - S.Qc i * n =
        (∑ p ∈ Finset.range n, g p - S.QJ i J * n) + ∑ p ∈ Finset.range n, (ξ p - g p) -
          (S.Qc i - S.QJ i J) * n := by
      rw [Finset.sum_sub_distrib]; ring
    rw [e]
    have h1 := hpre n hn
    obtain ⟨h2a, h2b⟩ := hdiff n hn
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn
    have h3 : (S.Qc i - S.QJ i J) * n ≤ η₃ * N :=
      mul_le_mul hQ hnN (Nat.cast_nonneg _) hη₃
    have h4 : 0 ≤ (S.Qc i - S.QJ i J) * n := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    rw [abs_le] at h1 ⊢
    constructor <;> nlinarith
  refine ⟨fun p => le_trans (hg0 p) (hgξ p), hQ0, by linarith, hmain, ?_⟩
  have := hmain N le_rfl
  rw [abs_le] at this
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  nlinarith

/-! ## The starting point -/

/-- **`IterHyp` at the starting point** (Proposition 12.27 (ii) of the paper): if the laws of large numbers hold on the interval of the free bits and on the interval of the Terras part (in the form of the conclusions of `lln_free_famX0`,
`lln_terras_famX0`; Lemma 12.16 of the paper), the sum of the tail is at most `θ N₀`, and `Q - Q_J ≤ η₃`, then `Ξ⁺` of each item satisfies `IterHyp`. -/
theorem iterHyp_x0 (β' : List Bool) (n u J : ℕ) (hKn : S.Kc + S.s' ≤ n) (hu : u < 2 ^ S.Flen n)
    {εL θ η₃ η : ℝ} (hεL : 0 ≤ εL)
    (hfree : ∀ (i : S.Item) x, Dfa.Reach (muStepB B) S.e x → ∀ p, S.Kc - 1 ≤ p → p ≤ S.Kc - 1 + S.Flen n →
      |W3d.wsum (muStepB B) J (S.phi i J) x
        ((binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).map W3d.f2b |>.drop (S.Kc - 1))
        (p - (S.Kc - 1)) - S.QJ i J * ((p - (S.Kc - 1) : ℕ) : ℝ)| ≤ εL * (S.Flen n : ℝ))
    (hter : ∀ (i : S.Item) x, Dfa.Reach (muStepB B) S.e x →
      ∀ p, n - 1 ≤ p → p ≤ n - 1 + ((parityOf (S.β₀ ++ β')).length - S.s') →
      |W3d.wsum (muStepB B) J (S.phi i J) x
        ((binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).map W3d.f2b |>.drop (n - 1))
        (p - (n - 1)) - S.QJ i J * ((p - (n - 1) : ℕ) : ℝ)| ≤
        εL * (((parityOf (S.β₀ ++ β')).length - S.s' : ℕ) : ℝ))
    (htail : ∀ i : S.Item, ∑ p ∈ Finset.range (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length,
      ∑ r ∈ Finset.Ioc J (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length,
        (S.xiI i r (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)) p : ℝ) ≤
          θ * (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length)
    (hQ : ∀ i : S.Item, S.Qc i - S.QJ i J ≤ η₃)
    (hη : εL * (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length +
        ((S.BJ J : ℝ) + S.Hb) * ((S.Kc - 1 + 2 * S.s' : ℕ) : ℝ) +
        θ * (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length +
        η₃ * (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length ≤
          η * (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length)
    (hη1 : η ≤ 1) :
    ∀ i : S.Item, W3a.IterHyp (S.Hb + 1) η (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length
      (S.XiHat i (binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u))) (S.Qc i) := by
  intro i
  have hωf := S.binWord_x0 β' hKn hu
  generalize hω : binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u) = ω at hfree hter htail hη hωf ⊢
  have hpre : S.β₀ <+: S.β₀ ++ β' := List.prefix_append _ _
  have hsm : S.s' ≤ (parityOf (S.β₀ ++ β')).length := fam_s_le hpre
  have hK1 : 1 ≤ S.Kc := by unfold Kc; omega
  have hN : ω.length = n + (parityOf (S.β₀ ++ β')).length - 1 := by
    rw [← hω, W3a.length_binWord]
    exact fam_lenT_X0 S.β₀ (S.β₀ ++ β') (by omega) hKn S.T0_bounds.1 S.T0_bounds.2 hu
  have hus : S.us.length ≤ S.Kc - 1 := S.us_le_Kc
  have hFn : S.Flen n = n - S.Kc - S.s' := rfl
  set g : ℕ → ℝ := fun p => if S.us.length ≤ p then (S.XiJ i J ω p : ℝ) else 0 with hg
  have hg0 : ∀ p, 0 ≤ g p := fun p => by simp only [hg]; split_ifs <;> positivity
  have hgB : ∀ p, g p ≤ S.BJ J := fun p => by
    simp only [hg]; split_ifs
    · exact_mod_cast S.XiJ_le_BJ i J ω p
    · positivity
  have hc : ∀ p, |g p - S.QJ i J| ≤ S.BJ J + S.Hb := by
    intro p
    have h1 := hg0 p; have h2 := hgB p
    have h3 := S.QJ_nonneg i J; have h4 := S.QJ_le_Hb i J
    rw [abs_le]; constructor <;> linarith
  have hreach : ∀ a, S.us.length ≤ a → Dfa.Reach (muStepB B) S.e (muZ B (ω.take a)) := by
    intro a ha; rw [hωf]; exact S.reach_of_ge _ ha
  have hIco : ∀ a q, S.us.length ≤ a → a ≤ q →
      ∑ p ∈ Finset.Ico a q, g p = ∑ p ∈ Finset.Ico a q, (S.XiJ i J ω p : ℝ) := by
    intro a q ha _
    refine Finset.sum_congr rfl (fun p hp => ?_)
    simp only [hg, show S.us.length ≤ p from le_trans ha (Finset.mem_Ico.mp hp).1, ↓reduceIte]
  -- the two intervals
  have hI₁ : ∀ q, S.Kc - 1 ≤ q → q ≤ S.Kc - 1 + S.Flen n →
      |∑ p ∈ Finset.Ico (S.Kc - 1) q, g p - S.QJ i J * ((q - (S.Kc - 1) : ℕ) : ℝ)| ≤ εL * (S.Flen n : ℝ) := by
    intro q hq1 hq2
    rw [hIco _ _ hus hq1, S.sum_Ico_XiJ i J ω hq1]
    exact hfree i _ (hreach _ hus) q hq1 hq2
  have hI₂ : ∀ q, n - 1 ≤ q → q ≤ n - 1 + ((parityOf (S.β₀ ++ β')).length - S.s') →
      |∑ p ∈ Finset.Ico (n - 1) q, g p - S.QJ i J * ((q - (n - 1) : ℕ) : ℝ)| ≤
        εL * (((parityOf (S.β₀ ++ β')).length - S.s' : ℕ) : ℝ) := by
    intro q hq1 hq2
    have hn1 : S.us.length ≤ n - 1 := by omega
    rw [hIco _ _ hn1 hq1, S.sum_Ico_XiJ i J ω hq1]
    exact hter i _ (hreach _ hn1) q hq1 hq2
  have hpre2 := prefix_two (f := g) (Q := S.QJ i J) (c := S.BJ J + S.Hb) (N := ω.length)
    (a₁ := S.Kc - 1) (b₁ := S.Kc - 1 + S.Flen n) (a₂ := n - 1)
    (b₂ := n - 1 + ((parityOf (S.β₀ ++ β')).length - S.s'))
    (by omega) (by omega) (by omega) (by omega) hc (by positivity) (by positivity) hI₁ hI₂
  have hout : S.Kc - 1 + (n - 1 - (S.Kc - 1 + S.Flen n)) +
      (ω.length - (n - 1 + ((parityOf (S.β₀ ++ β')).length - S.s'))) = S.Kc - 1 + 2 * S.s' := by
    omega
  rw [hout] at hpre2
  have hlen : (S.Flen n : ℝ) + (((parityOf (S.β₀ ++ β')).length - S.s' : ℕ) : ℝ) ≤ ω.length := by
    have : S.Flen n + ((parityOf (S.β₀ ++ β')).length - S.s') ≤ ω.length := by omega
    exact_mod_cast this
  -- the tail
  have htl : ∑ p ∈ Finset.range ω.length, (S.XiHat i ω p - g p) ≤ θ * ω.length := by
    refine le_trans (Finset.sum_le_sum (fun p _ => ?_)) (htail i)
    unfold XiHat
    simp only [hg]
    split_ifs
    · have := S.XiP_le_XiJ_add i J ω p
      have h' : ((S.XiJ i ω.length ω p : ℕ) : ℝ) ≤ (S.XiJ i J ω p : ℝ) +
          ∑ r ∈ Finset.Ioc J ω.length, (S.xiI i r ω p : ℝ) := by exact_mod_cast this
      linarith
    · simp only [sub_self]
      exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  refine S.iterHyp_of_parts i J ω.length (S.XiHat i ω) g hg0 (fun p => ?_) hpre2 htl (hQ i) ?_ hη1
  · unfold XiHat
    simp only [hg]
    split_ifs
    · exact_mod_cast S.XiJ_le_XiP i J ω p
    · exact le_rfl
  · have h1 : εL * (S.Flen n : ℝ) + εL * (((parityOf (S.β₀ ++ β')).length - S.s' : ℕ) : ℝ) ≤
        εL * ω.length := by rw [← mul_add]; exact mul_le_mul_of_nonneg_left hlen hεL
    linarith

/-! ## The end point -/

/-- `IterHyp` from prefix sums. -/
theorem iterHyp_of_prefix {η Q : ℝ} {N : ℕ} {ξ : ℕ → ℝ} (hξ : ∀ p, 0 ≤ ξ p) (hQ0 : 0 ≤ Q) (hQ : Q ≤ S.Hb)
    (hpre : ∀ n ≤ N, |∑ p ∈ Finset.range n, ξ p - Q * n| ≤ η * N) (hη1 : η ≤ 1) :
    W3a.IterHyp (S.Hb + 1) η N ξ Q := by
  refine ⟨hξ, hQ0, by linarith, hpre, ?_⟩
  have := hpre N le_rfl
  rw [abs_le] at this
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  nlinarith

/-- The good positions of the end point: the interval `[a₁, a₁ + b)` of the low part of `h`, and the part `[a₂, a₂ + F - M)` of the middle digits `ϖ` in which a range `M` fits
(`a₂ = a₁ + b + K`). -/
def GoodX1 (a₁ b F M p : ℕ) : Prop :=
  (a₁ ≤ p ∧ p < a₁ + b) ∨ (a₁ + b + S.Kc ≤ p ∧ p < a₁ + b + S.Kc + (F - M))

instance (a₁ b F M : ℕ) : DecidablePred (S.GoodX1 a₁ b F M) := fun p => by
  unfold GoodX1; infer_instance

/-- **`IterHyp` at the end point** (Proposition 12.28 (ii) of the paper): if the window sums on the two intervals are close to `Q_M`, then `Ξ^{(M)}` restricted to the good positions satisfies `IterHyp`. -/
theorem iterHyp_x1 (ω₁ m₁ : List (Fin 2)) (hω₁ : ω₁ = fullW S.us [] S.y'' S.z m₁ S.R) (a₁ b F M : ℕ)
    (ha₁ : S.us.length ≤ a₁) (hlen : ω₁.length = a₁ + b + S.Kc + F + S.s') {ε' η : ℝ} (hε' : 0 ≤ ε')
    (hlow : ∀ (i : S.Item) x, Dfa.Reach (muStepB B) S.e x → ∀ q, a₁ ≤ q → q ≤ a₁ + b →
      |W3d.wsum (muStepB B) M (S.phi i M) x ((ω₁.map W3d.f2b).drop a₁) (q - a₁) -
        S.QJ i M * ((q - a₁ : ℕ) : ℝ)| ≤ ε' * (b : ℝ))
    (hmid : ∀ (i : S.Item) x, Dfa.Reach (muStepB B) S.e x → ∀ q, a₁ + b + S.Kc ≤ q → q ≤ a₁ + b + S.Kc + F →
      |W3d.wsum (muStepB B) M (S.phi i M) x ((ω₁.map W3d.f2b).drop (a₁ + b + S.Kc)) (q - (a₁ + b + S.Kc)) -
        S.QJ i M * ((q - (a₁ + b + S.Kc) : ℕ) : ℝ)| ≤ ε' * (F : ℝ))
    (hη : ε' * (b : ℝ) + ε' * (F : ℝ) + ((S.BJ M : ℝ) + S.Hb) * ((a₁ + S.Kc + M + S.s' : ℕ) : ℝ) ≤
      η * ω₁.length) (hη1 : η ≤ 1) :
    ∀ i : S.Item, W3a.IterHyp (S.Hb + 1) η ω₁.length
      (fun p => if S.GoodX1 a₁ b F M p then (S.XiJ i M ω₁ p : ℝ) else 0) (S.QJ i M) := by
  intro i
  set ξ : ℕ → ℝ := fun p => if S.GoodX1 a₁ b F M p then (S.XiJ i M ω₁ p : ℝ) else 0 with hξ
  have hξ0 : ∀ p, 0 ≤ ξ p := fun p => by simp only [hξ]; split_ifs <;> positivity
  have hξB : ∀ p, ξ p ≤ S.BJ M := fun p => by
    simp only [hξ]; split_ifs
    · exact_mod_cast S.XiJ_le_BJ i M ω₁ p
    · positivity
  have hc : ∀ p, |ξ p - S.QJ i M| ≤ S.BJ M + S.Hb := by
    intro p
    have h1 := hξ0 p; have h2 := hξB p
    have h3 := S.QJ_nonneg i M; have h4 := S.QJ_le_Hb i M
    rw [abs_le]; constructor <;> linarith
  have hreach : ∀ a, S.us.length ≤ a → Dfa.Reach (muStepB B) S.e (muZ B (ω₁.take a)) := by
    intro a ha; rw [hω₁]; exact S.reach_of_ge _ ha
  have hI₁ : ∀ q, a₁ ≤ q → q ≤ a₁ + b →
      |∑ p ∈ Finset.Ico a₁ q, ξ p - S.QJ i M * ((q - a₁ : ℕ) : ℝ)| ≤ ε' * (b : ℝ) := by
    intro q hq1 hq2
    have e : ∑ p ∈ Finset.Ico a₁ q, ξ p = ∑ p ∈ Finset.Ico a₁ q, (S.XiJ i M ω₁ p : ℝ) := by
      refine Finset.sum_congr rfl (fun p hp => ?_)
      have hp' := Finset.mem_Ico.mp hp
      simp only [hξ, show S.GoodX1 a₁ b F M p from Or.inl ⟨hp'.1, by omega⟩, ↓reduceIte]
    rw [e, S.sum_Ico_XiJ i M ω₁ hq1]
    exact hlow i _ (hreach _ ha₁) q hq1 hq2
  have hI₂ : ∀ q, a₁ + b + S.Kc ≤ q → q ≤ a₁ + b + S.Kc + (F - M) →
      |∑ p ∈ Finset.Ico (a₁ + b + S.Kc) q, ξ p - S.QJ i M * ((q - (a₁ + b + S.Kc) : ℕ) : ℝ)| ≤
        ε' * (F : ℝ) := by
    intro q hq1 hq2
    have e : ∑ p ∈ Finset.Ico (a₁ + b + S.Kc) q, ξ p =
        ∑ p ∈ Finset.Ico (a₁ + b + S.Kc) q, (S.XiJ i M ω₁ p : ℝ) := by
      refine Finset.sum_congr rfl (fun p hp => ?_)
      have hp' := Finset.mem_Ico.mp hp
      simp only [hξ, show S.GoodX1 a₁ b F M p from Or.inr ⟨hp'.1, by omega⟩, ↓reduceIte]
    rw [e, S.sum_Ico_XiJ i M ω₁ hq1]
    exact hmid i _ (hreach _ (by omega)) q hq1 (by omega)
  have hpre2 := prefix_two (f := ξ) (Q := S.QJ i M) (c := S.BJ M + S.Hb) (N := ω₁.length)
    (a₁ := a₁) (b₁ := a₁ + b) (a₂ := a₁ + b + S.Kc) (b₂ := a₁ + b + S.Kc + (F - M))
    (by omega) (by omega) (by omega) (by omega) hc (by positivity) (by positivity) hI₁ hI₂
  have hout : a₁ + (a₁ + b + S.Kc - (a₁ + b)) + (ω₁.length - (a₁ + b + S.Kc + (F - M))) ≤
      a₁ + S.Kc + M + S.s' := by omega
  have hc0 : (0 : ℝ) ≤ S.BJ M + S.Hb := le_trans (abs_nonneg _) (hc 0)
  refine S.iterHyp_of_prefix hξ0 (S.QJ_nonneg i M) (S.QJ_le_Hb i M) (fun n hn => ?_) hη1
  refine le_trans (hpre2 n hn) ?_
  have : ((S.BJ M : ℝ) + S.Hb) * ((a₁ + (a₁ + b + S.Kc - (a₁ + b)) +
      (ω₁.length - (a₁ + b + S.Kc + (F - M))) : ℕ) : ℝ) ≤
      ((S.BJ M : ℝ) + S.Hb) * ((a₁ + S.Kc + M + S.s' : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hout) hc0
  linarith

/-- The good positions of the end point lie in the middle word, and a range `M` fits. -/
theorem goodX1_mem (m₁ : List (Fin 2)) {a₁ b F M : ℕ} (hτ : S.τ.length ≤ a₁)
    (hlen : S.τ.length + m₁.length = a₁ + b + S.Kc + F) (hM : M ≤ F) :
    ∀ p, S.GoodX1 a₁ b F M p → S.τ.length ≤ p ∧ p + M ≤ S.τ.length + m₁.length := by
  intro p hp
  unfold GoodX1 at hp
  omega

/-- **The word of the end point**: if the top window is `τ` and the length of the high part of `h` is at least `E`, then `binWord x₁ = τ · m₁ · y''(u♯)^R z`,
`|τ| + |m₁| = a₁ + b + K + F` (`a₁ := lenT ⌊h/2^b⌋`). -/
theorem binWord_x1 (β' : List Bool) {n u b : ℕ} (hKn : S.Kc + S.s' ≤ n)
    (hA : 1 ≤ terrasA (parityOf (S.β₀ ++ β')))
    (hb : 2 ^ b ≤ famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u / 2 ^ n)
    (hlenh : S.E ≤ lenT (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u / 2 ^ n / 2 ^ b))
    (htop : (binWord (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).take S.E = S.τ) :
    ∃ m₁ : List (Fin 2), binWord (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u) = fullW S.us [] S.y'' S.z m₁ S.R ∧
      S.τ.length + m₁.length =
        lenT (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u / 2 ^ n / 2 ^ b) + b + S.Kc + S.Flen n ∧
      (binWord (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u)).length =
        lenT (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u / 2 ^ n / 2 ^ b) + b + S.Kc + S.Flen n + S.s' := by
  have hK1 : 1 ≤ S.Kc := by unfold Kc; omega
  have hsplit := binTail_x1_split (β₀ := S.β₀) (β := S.β₀ ++ β') (n := n) (K := S.Kc) (τ := S.T0) (u := u) b hK1
    hKn S.T0_bounds.1 hA hb
  set P := binTail (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u / 2 ^ n / 2 ^ b)
      ++ bitsMSB b (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u / 2 ^ n % 2 ^ b)
      ++ bitsMSB S.Kc (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u % 2 ^ n / 2 ^ (n - S.Kc))
      ++ bitsMSB (n - S.Kc - (parityOf S.β₀).length)
          (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u % 2 ^ n % 2 ^ (n - S.Kc) / 2 ^ (parityOf S.β₀).length)
    with hP
  have hPlen : (P.map W3a.l2f).length =
      lenT (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u / 2 ^ n / 2 ^ b) + b + S.Kc + S.Flen n := by
    simp only [hP, List.length_map, List.length_append, bitsMSB_length]; rfl
  have hw : binWord (famX1 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u) = P.map W3a.l2f ++ (S.y'' ++ S.τ ++ S.z) := by
    rw [W3a.binWord_eq_map, hsplit, List.map_append, S.hy, S.tailW_eq]
  have hEP : S.E ≤ (P.map W3a.l2f).length := by rw [hPlen]; omega
  have htake : (P.map W3a.l2f).take S.E = S.τ := by
    rw [hw, List.take_append_of_le_length hEP] at htop; exact htop
  have hEτ : S.E = S.τ.length := rfl
  refine ⟨(P.map W3a.l2f).drop S.E, ?_, ?_, ?_⟩
  · rw [hw, S.fullW_eq]
    conv_lhs => rw [← List.take_append_drop S.E (P.map W3a.l2f), htake]
  · rw [List.length_drop, hPlen, ← hEτ]; omega
  · have hs : (S.y'' ++ S.τ ++ S.z).length = S.s' := by
      rw [← S.tailW_eq, ← S.hy, List.length_map, bitsMSB_length]; rfl
    rw [hw, List.length_append, hPlen, hs]

end Setup

end Collatz.Arctic.NatQ5.W3h
