/-
# Case B: small parts of the assembly (Proposition 12.31 of the paper)

Small parts for choosing the constants in the order of quantifiers (Step 1 of the proof of Proposition 12.31 of the paper).

* `ev_ge`: `A ≤ c k` (`c > 0`) holds if `k` is large.
* `exists_J_Q`, `exists_M`: the choice of the truncations `J` and `M` (`Q_J → Q`, `C^{(M)} → C`).
* `prσ_four`: the joint probability of the four events on the side of σ.
* `conf_mid0_split`: the configuration of the starting point is obtained from the state after reading the free bits by reading `w (u♯)^R`.
* `KT`, `KT_spec`, `KT_lin`: the length `K_r := ⌊L_r/(11g)⌋ - 2` of the runs in `RunMiss` on the Terras part.
-/
import CollatzProof.Arctic.Nat.W3hCaseBX

namespace Collatz.Arctic.NatQ5.W3h

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W3c
open Collatz.Arctic.MinIdeal (BRel)
open Filter Topology

set_option linter.unusedSectionVars false

theorem ev_ge (A c : ℝ) (hc : 0 < c) : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → A ≤ c * k := by
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (A / c)
  refine ⟨k₀, fun k hk => ?_⟩
  have : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : A / c < k := lt_of_lt_of_le hk₀ this
  rw [div_lt_iff₀ hc] at h1
  linarith

/-- The joint probability of the four events on the side of σ. -/
theorem prσ_four (β₀ : List Bool) (k : ℕ) (E₁ E₂ E₃ E₄ : List Bool → Prop) {c η : ℚ}
    (h1 : c ≤ Prσ β₀ k E₁) (h2 : 1 - η ≤ Prσ β₀ k E₂) (h3 : 1 - η ≤ Prσ β₀ k E₃) (h4 : 1 - η ≤ Prσ β₀ k E₄) :
    c - 3 * η ≤ Prσ β₀ k (fun β => ((E₁ β ∧ E₂ β) ∧ E₃ β) ∧ E₄ β) := by
  have hw := W3b.sum_wt k
  have a1 := Prσ_and_ge β₀ k E₁ E₂ wtβ_nonneg
  have a2 := Prσ_and_ge β₀ k (fun β => E₁ β ∧ E₂ β) E₃ wtβ_nonneg
  have a3 := Prσ_and_ge β₀ k (fun β => (E₁ β ∧ E₂ β) ∧ E₃ β) E₄ wtβ_nonneg
  rw [hw] at a1 a2 a3
  linarith

theorem prσ_not_ge {β₀ : List Bool} {k : ℕ} {E : List Bool → Prop} {η : ℚ} (h : Prσ β₀ k E ≤ η) :
    1 - η ≤ Prσ β₀ k (fun β => ¬ E β) := by
  rw [prσ_not]; linarith

/-- If the good set is larger than the sum of the sizes of the bad sets, some good element lies in no bad set. -/
theorem exists_avoid (G B₁ B₂ B₃ B₄ : Finset ℕ) {x : ℝ} (hG : x ≤ G.card)
    (hB : (B₁.card : ℝ) + B₂.card + B₃.card + B₄.card < x) :
    ∃ u ∈ G, u ∉ B₁ ∧ u ∉ B₂ ∧ u ∉ B₃ ∧ u ∉ B₄ := by
  classical
  by_contra hc
  push Not at hc
  have hsub : G ⊆ B₁ ∪ B₂ ∪ B₃ ∪ B₄ := by
    intro u hu
    by_cases h1 : u ∈ B₁
    · simp [h1]
    by_cases h2 : u ∈ B₂
    · simp [h2]
    by_cases h3 : u ∈ B₃
    · simp [h3]
    · simp [hc u hu h1 h2 h3]
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (B₁ ∪ B₂ ∪ B₃) B₄
  have h3 := Finset.card_union_le (B₁ ∪ B₂) B₃
  have h4 := Finset.card_union_le B₁ B₂
  have : (G.card : ℝ) ≤ B₁.card + B₂.card + B₃.card + B₄.card := by exact_mod_cast (by omega)
  linarith

/-- The form of `exists_avoid` with upper bounds for the sizes as hypotheses (bounds in `ℚ` and in `ℝ`). -/
theorem exists_avoid' {G B₁ B₂ B₃ B₄ : Finset ℕ} {x c₂ : ℝ} {c₁ c₃ c₄ : ℚ} (hG : x ≤ G.card)
    (h₁ : (B₁.card : ℚ) ≤ c₁) (h₂ : (B₂.card : ℝ) ≤ c₂) (h₃ : (B₃.card : ℚ) ≤ c₃) (h₄ : (B₄.card : ℚ) ≤ c₄)
    (hsum : (c₁ : ℝ) + c₂ + c₃ + c₄ < x) :
    ∃ u ∈ G, u ∉ B₁ ∧ u ∉ B₂ ∧ u ∉ B₃ ∧ u ∉ B₄ := by
  have h₁' : (B₁.card : ℝ) ≤ c₁ := by exact_mod_cast h₁
  have h₃' : (B₃.card : ℝ) ≤ c₃ := by exact_mod_cast h₃
  have h₄' : (B₄.card : ℝ) ≤ c₄ := by exact_mod_cast h₄
  exact exists_avoid G B₁ B₂ B₃ B₄ hG (by linarith)

/-- The arithmetic of the sum of the numbers of bad `u`. -/
theorem bad_sum (F Lc : ℕ) (hF : Lc ≤ F) {η₀ εF : ℝ} {TV : ℚ} (hη₀ : 0 < η₀)
    (hεF : εF ≤ η₀ / 8 * (1 / 2 ^ (Lc + 4))) (hTV : TV ≤ 1 / 2 ^ (Lc + 4)) :
    (((1 / 2 ^ (Lc + 4) * 2 ^ F : ℚ)) : ℝ) + εF / (η₀ / 8) * 2 ^ F + ((1 / 2 ^ (Lc + 4) * 2 ^ F : ℚ) : ℝ) +
      (((1 / 2 ^ (Lc + 4) + (3 / 2 ^ (Lc + 6) + TV)) * 2 ^ F : ℚ) : ℝ) < 2 ^ (F - Lc) := by
  have hTVr : (TV : ℝ) ≤ 1 / 2 ^ (Lc + 4) := by
    have := (Rat.cast_le (K := ℝ)).mpr hTV; push_cast at this; exact this
  push_cast
  set u : ℝ := 1 / 2 ^ (Lc + 4) with hu
  have hu0 : 0 < u := by positivity
  have hθ : εF / (η₀ / 8) ≤ u := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have h64 : (3 : ℝ) / 2 ^ (Lc + 6) = 3 / 4 * u := by
    rw [hu, pow_add, pow_add]; field_simp; norm_num
  have e2 : (2 : ℝ) ^ (F - Lc) = 2 ^ F * (16 * u) := by
    have e1 : ((2 : ℝ) ^ (F - Lc)) * 2 ^ Lc = 2 ^ F := by rw [← pow_add]; congr 1; omega
    rw [hu, ← e1, pow_add]; field_simp; norm_num
  have hF0 : (0 : ℝ) < 2 ^ F := by positivity
  have hX : εF / (η₀ / 8) * 2 ^ F ≤ u * 2 ^ F := mul_le_mul_of_nonneg_right hθ hF0.le
  have hY : (u + (3 / 2 ^ (Lc + 6) + (TV : ℝ))) * 2 ^ F ≤ (u + (3 / 4 * u + u)) * 2 ^ F := by
    rw [h64]; exact mul_le_mul_of_nonneg_right (by linarith) hF0.le
  rw [e2]
  nlinarith

/-- `(1 + κ) N₀ ≤ N₁` from the expansion of lengths. -/
theorem len_ratio {N₀ N₁ k j : ℕ} {κ c : ℝ} (h1 : N₀ + j ≤ N₁) (h2 : c * k ≤ j) (h3 : N₀ ≤ 34 * k)
    (hκ : κ ≤ c / 34) (hκ0 : 0 ≤ κ) : (1 + κ) * (N₀ : ℝ) ≤ N₁ := by
  have h1' : (N₀ : ℝ) + j ≤ N₁ := by exact_mod_cast h1
  have h3' : (N₀ : ℝ) ≤ 34 * k := by exact_mod_cast h3
  have hN0 : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
  have h4 : κ * (N₀ : ℝ) ≤ c / 34 * (34 * k) := by
    have hc : 0 ≤ c / 34 := le_trans hκ0 hκ
    calc κ * (N₀ : ℝ) ≤ c / 34 * N₀ := mul_le_mul_of_nonneg_right hκ hN0
      _ ≤ c / 34 * (34 * k) := mul_le_mul_of_nonneg_left h3' hc
  have e : c / 34 * (34 * (k : ℝ)) = c * k := by ring
  linarith

/-- The form `K (C (η + 1/k)) ≤ 2 δ`. -/
theorem err_k {K C η δ : ℝ} {k : ℕ} (hk : 1 ≤ k) (h1 : K * C * η ≤ δ) (h2 : K * C ≤ δ * k) :
    K * (C * (η + 1 / k)) ≤ δ + δ := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have : K * C / k ≤ δ := by rw [div_le_iff₀ hk0]; linarith
  have e : K * (C * (η + 1 / k)) = K * C * η + K * C / k := by ring
  rw [e]; linarith

namespace Setup

variable {Q : Type} [Fintype Q] [DecidableEq Q] {B : ValAuto Q} (S : Setup B)

/-- The choice of the truncation `J`: `Q - Q_J ≤ η` (for all items). -/
theorem exists_J_Q {η : ℝ} (hη : 0 < η) : ∃ J₀ : ℕ, ∀ J, J₀ ≤ J → ∀ i : S.Item, S.Qc i - S.QJ i J ≤ η := by
  have h : ∀ i : S.Item, ∃ J₀ : ℕ, ∀ J, J₀ ≤ J → S.Qc i - η < S.QJ i J := by
    intro i
    have := (tendsto_order.1 (S.tendsto_QJ i)).1 (S.Qc i - η) (by linarith)
    exact eventually_atTop.1 this
  choose J₀ hJ₀ using h
  refine ⟨Finset.univ.sup J₀, fun J hJ i => ?_⟩
  have := hJ₀ i J (le_trans (Finset.le_sup (f := J₀) (Finset.mem_univ i)) hJ)
  linarith

/-- The choice of the truncation `M`: `C^{(M)}_d(c) ≥ C_d(c) - ε` (for all configurations of `𝔎` and all `d ≤ D`). -/
theorem exists_M {ε : ℝ} (hε : 0 < ε) : ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → ∀ c ∈ S.Kset, ∀ d ≤ S.Dm,
    S.coef d c.1 - ε ≤ S.coefM M d c.1 := by
  have h : ∀ x : PSt B × ℕ, ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → S.coef x.2 x.1.1 - ε < S.coefM M x.2 x.1.1 := by
    intro x
    have := (tendsto_order.1 (S.tendsto_coefM x.2 x.1.1)).1 (S.coef x.2 x.1.1 - ε) (by linarith)
    exact eventually_atTop.1 this
  choose M₀ hM₀ using h
  refine ⟨(S.Kset ×ˢ Finset.range (S.Dm + 1)).sup M₀, fun M hM c hc d hd => ?_⟩
  have hmem : (c, d) ∈ S.Kset ×ˢ Finset.range (S.Dm + 1) :=
    Finset.mem_product.mpr ⟨hc, Finset.mem_range.mpr (by omega)⟩
  exact (hM₀ (c, d) M (le_trans (Finset.le_sup (f := M₀) hmem) hM)).le

/-- Computation of the configuration of the starting point. -/
theorem conf_mid0_split (β' : List Bool) (n u : ℕ) :
    S.conf (S.mid0 (S.β₀ ++ β') n u) =
      ((bitsMSB S.s' (famRho S.β₀ (S.β₀ ++ β'))).map W3a.l2f ++ TwOf S.β₀ β' ++ S.y'' ++ S.τ).foldl (stepF B)
        (((bitsMSB (S.Flen n) u).map W3a.l2f).foldl (stepF B) S.P1) := by
  unfold conf mid0 P1
  simp only [List.foldl_append, TwOf, s']

/-- The sum of `K_s` over `𝔎`. -/
noncomputable def Kmax : ℝ := ∑ c ∈ S.Kset, S.Ktot c.1

theorem Ktot_le_Kmax {c : PSt B} (hc : c ∈ S.Kset) : S.Ktot c.1 ≤ S.Kmax :=
  Finset.single_le_sum (f := fun c : PSt B => S.Ktot c.1) (fun c _ => S.Ktot_nonneg c.1) hc

/-- Rewriting the sums of `RunMiss` between `ℚ` and `ℝ`. -/
theorem runMiss_cast (I Rs : Finset ℕ) (g : ℕ) (P : ℕ → ℕ → Prop) [∀ i r, Decidable (P i r)] :
    (22 * (g : ℝ)) * ∑ j ∈ I, ∑ r ∈ Rs, S.wt r * (if P j r then 1 else 0) =
      ((∑ j ∈ I, ∑ r ∈ Rs, ((22 * g * S.D.cP : ℕ) : ℚ) * ((r : ℚ) + 1) ^ (S.D.dP + 1) *
        (if P j r then 1 else 0) : ℚ) : ℝ) := by
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [S.wt_eq]
  split_ifs <;> ring

/-- The length of the runs in `RunMiss` on the Terras part. -/
def KT (g r : ℕ) : ℕ := S.Lr S.C0 r / (11 * g) - 2

theorem KT_spec {g r : ℕ} (hg : 1 ≤ g) (hr : S.cW' * (S.C0 + 66 * g + 1) ≤ r) :
    1 ≤ S.KT g r ∧ 11 * g * (S.KT g r + 2) ≤ S.Lr S.C0 r := by
  have hc := S.cW'_pos
  have h1 : S.C0 + 66 * g + 1 ≤ r / S.cW' := by
    rw [Nat.le_div_iff_mul_le (by omega)]; rw [mul_comm]; exact hr
  have h2 : 33 * g ≤ S.Lr S.C0 r := by
    unfold Lr ell0
    generalize r / S.cW' = x at h1
    omega
  have h3 : 3 ≤ S.Lr S.C0 r / (11 * g) := by
    rw [Nat.le_div_iff_mul_le (by omega)]; linarith
  refine ⟨by unfold KT; omega, ?_⟩
  unfold KT
  have h4 := Nat.div_mul_le_self (S.Lr S.C0 r) (11 * g)
  have : S.Lr S.C0 r / (11 * g) - 2 + 2 = S.Lr S.C0 r / (11 * g) := by omega
  rw [this, mul_comm]; exact h4

theorem Lr_le (r : ℕ) : S.Lr S.C0 r ≤ r := by
  have hc := S.cW'_pos
  have : r / S.cW' ≤ r := Nat.div_le_self _ _
  unfold Lr ell0; omega

theorem KT_le (g r : ℕ) : S.KT g r ≤ r := by
  unfold KT
  have := S.Lr_le r
  have : S.Lr S.C0 r / (11 * g) ≤ S.Lr S.C0 r := Nat.div_le_self _ _
  omega

theorem KT_lin {g : ℕ} (hg : 1 ≤ g) (R : ℕ) :
    R ≤ 2 * S.cW' * (11 * g) * S.KT g R + (2 * (2 * S.cW' * (11 * g)) + S.cW' * (2 * (11 * g) + S.C0 + 3)) := by
  have h := S.Lr_lin S.C0 (11 * g) R (by omega)
  unfold KT
  have h2 : S.Lr S.C0 R / (11 * g) ≤ S.Lr S.C0 R / (11 * g) - 2 + 2 := by omega
  have h3 := Nat.mul_le_mul_left (2 * S.cW' * (11 * g)) h2
  rw [mul_add] at h3
  omega

end Setup

end Collatz.Arctic.NatQ5.W3h
