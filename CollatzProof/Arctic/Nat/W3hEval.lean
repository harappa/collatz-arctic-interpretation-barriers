/-
# Evaluation of the points: the deterministic forms of Propositions 12.27 (i) and 12.28 (i) of the paper

Propositions 12.27 (i) and 12.28 (i) of the paper as deterministic inequalities, with the hypothesis (IH) of Lemma 12.15 (`W3a.IterHyp`) as a premise. `IterHyp` is derived
from the probabilistic events in `W3hCaseB.lean`.

* **Window sums** (`wsum_phi`): the `wsum` of `W3d` (for the DFA of forward states and the window function `phi i J`) is the sum over an interval of the truncated weights of detours of the point word,
  `XiJ i J ω p := Σ_{r ∈ [1, J]} ξ(r, p)`.
* **Upper bound at the starting point** (`aval_le_of_iterHyp`, of the form of Proposition 12.27 (i)): if the coefficients above `d₀` of the forward state `s` of the configuration vanish and, for every item,
  `Ξ⁺` (restricted to `p ≥ |u♯|`) satisfies `IterHyp Bv η N · (Qc i)`, then
  `V ≤ Σ_{d ≤ d₀} C_d(s) N^d + K_s · 3^{D}(Bv+1)^{D}(η + 1/N) · N^{d₀}` (`D` is the maximal degree, `K_s := Σ κ`).
  The terms of degree above `d₀` vanish by degeneration (`degen`, `t₀ ≥ |u♯|`).
* **Lower bound at the end point** (`aval_ge_of_iterHyp`, of the form of Proposition 12.28 (i)): if `Ξ^{(M)}`, restricted to the good positions (`|τ| ≤ p`, `p + M ≤ |τ| + |m|`),
  satisfies `IterHyp Bv η N · (QJ i M)` and is `≤ B'`, then the part of degree `d` satisfies
  `V ≥ C^{(M)}_d(s) N^d - K_s (ε_d N^d + (d-1)(M-1) B'^d N^{d-1})` (`C^{(M)}` is the coefficient `coefM` with the means `Q_M`).
-/
import CollatzProof.Arctic.Nat.W3hSum

namespace Collatz.Arctic.NatQ5.W3h

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W3c
open Collatz.Arctic.MinIdeal (BRel)
open Filter Topology

set_option linter.unusedSectionVars false

namespace Setup

variable {Q : Type} [Fintype Q] [DecidableEq Q] {B : ValAuto Q} (S : Setup B)

/-! ## §1 Truncated weights of detours and window sums -/

/-- The weight `ξ_i(r, p)` of the detours of range `r` of the item `i`. -/
noncomputable def xiI (i : S.Item) (r : ℕ) (ω : List (Fin 2)) (p : ℕ) : ℕ :=
  xiOf B S.D.labS (S.D.g i.1 i.2.1) i.2.2 r ω p

/-- The weight of detours truncated to the ranges `[1, J]`. -/
noncomputable def XiJ (i : S.Item) (J : ℕ) (ω : List (Fin 2)) (p : ℕ) : ℕ :=
  ∑ r ∈ Finset.Icc 1 J, S.xiI i r ω p

theorem XiJ_eq_XiLe (i : S.Item) (J : ℕ) (ω : List (Fin 2)) (p : ℕ) :
    S.XiJ i J ω p = XiLe B S.D.labS (S.D.g i.1 i.2.1) i.2.2 J ω p := rfl

theorem XiP_eq (i : S.Item) (ω : List (Fin 2)) (p : ℕ) :
    XiP B S.D.labS (S.D.g i.1 i.2.1) i.2.2 ω p = S.XiJ i ω.length ω p := rfl

/-- The value of the window function is the truncated weight of detours. -/
theorem phiN_eq_XiJ (i : S.Item) (J : ℕ) (ω : List (Fin 2)) (p : ℕ) :
    S.phiN i J (muZ B (ω.take p)) (((ω.drop p).take J).map W3d.f2b) = S.XiJ i J ω p := by
  unfold phiN XiJ xiI xiOf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  have hrJ := (Finset.mem_Icc.mp hr).2
  have e : ((((ω.drop p).take J).map W3d.f2b).map W3d.b2f).take r = (ω.drop p).take r := by
    rw [List.map_map]
    have : (W3d.b2f ∘ W3d.f2b) = id := funext W3d.b2f_f2b
    rw [this, List.map_id, List.take_take, Nat.min_eq_left hrJ]
  rw [e]
  rfl

/-- **Window sums**: the `wsum` of `W3d` is the sum over an interval of the truncated weights of detours. -/
theorem wsum_phi (i : S.Item) (J : ℕ) (ω : List (Fin 2)) (a L : ℕ) :
    W3d.wsum (muStepB B) J (S.phi i J) (muZ B (ω.take a)) ((ω.map W3d.f2b).drop a) L =
      ∑ q ∈ Finset.range L, (S.XiJ i J ω (a + q) : ℝ) := by
  unfold W3d.wsum
  refine Finset.sum_congr rfl (fun q _ => ?_)
  have h1 : ((ω.map W3d.f2b).drop a).take q = ((ω.drop a).take q).map W3d.f2b := by
    rw [← List.map_drop, ← List.map_take]
  have h2 : (((ω.map W3d.f2b).drop a).drop q).take J = ((ω.drop (a + q)).take J).map W3d.f2b := by
    rw [← List.map_drop, ← List.map_drop, List.drop_drop, ← List.map_take]
  have h3 : Dfa.run (muStepB B) (muZ B (ω.take a)) (((ω.drop a).take q).map W3d.f2b) = muZ B (ω.take (a + q)) := by
    have := run_muStepB B (muZ B (ω.take a)) ((ω.drop a).take q)
    refine this.trans ?_
    rw [← muZ_append, ← List.take_add]
  unfold phi
  rw [h1, h2, h3, S.phiN_eq_XiJ]

/-- `Ξ^{(J)} ≤ Ξ⁺` (`p < N`): a detour whose range exceeds `N - p` has too short a window and weight 0. -/
theorem XiJ_le_XiP (i : S.Item) (J : ℕ) (ω : List (Fin 2)) (p : ℕ) :
    S.XiJ i J ω p ≤ S.XiJ i ω.length ω p := by
  unfold XiJ
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 J) (fun r => r ≤ ω.length) (S.xiI i · ω p)
  have hzero : ∑ r ∈ (Finset.Icc 1 J).filter (fun r => ¬ r ≤ ω.length), S.xiI i r ω p = 0 := by
    refine Finset.sum_eq_zero (fun r hr => ?_)
    rw [Finset.mem_filter] at hr
    unfold xiI xiOf
    have : S.D.g i.1 i.2.1 i.2.2 r ((ω.drop p).take r) = 0 := by
      by_contra hne
      have := S.D.g_len i.1 i.2.1 i.2.2 r _ hne
      rw [List.length_take, List.length_drop] at this
      omega
    rw [this, mul_zero]
  rw [← hsplit, hzero, add_zero]
  refine Finset.sum_le_sum_of_subset (fun r hr => ?_)
  rw [Finset.mem_filter, Finset.mem_Icc] at hr
  exact Finset.mem_Icc.mpr ⟨hr.1.1, hr.2⟩

/-- `Ξ⁺ ≤ Ξ^{(J)} + Σ_{r ∈ (J, N]} ξ`. -/
theorem XiP_le_XiJ_add (i : S.Item) (J : ℕ) (ω : List (Fin 2)) (p : ℕ) :
    S.XiJ i ω.length ω p ≤ S.XiJ i J ω p + ∑ r ∈ Finset.Ioc J ω.length, S.xiI i r ω p := by
  unfold XiJ
  calc ∑ r ∈ Finset.Icc 1 ω.length, S.xiI i r ω p
      ≤ ∑ r ∈ Finset.Icc 1 J ∪ Finset.Ioc J ω.length, S.xiI i r ω p := by
        refine Finset.sum_le_sum_of_subset (fun r hr => ?_)
        rw [Finset.mem_Icc] at hr
        by_cases h : r ≤ J
        · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hr.1, h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_Ioc.mpr ⟨by omega, hr.2⟩)
    _ ≤ _ := by
        have := Finset.sum_union_inter (s₁ := Finset.Icc 1 J) (s₂ := Finset.Ioc J ω.length)
          (f := fun r => S.xiI i r ω p)
        omega

/-! ## §2 Regrouping the coefficients -/

/-- The maximal degree. -/
noncomputable def Dm : ℕ := Finset.univ.sup S.D.deg

theorem deg_le_Dm (γ : S.D.Γ) : S.D.deg γ ≤ S.Dm := Finset.le_sup (f := S.D.deg) (Finset.mem_univ γ)

/-- The total `K_s` of `κ`. -/
noncomputable def Ktot (s : BRel (ZIdx B)) : ℝ :=
  ∑ γ, ∑ l : Fin (S.D.deg γ) → S.D.Lab, (S.D.κ γ s l : ℝ)

theorem Ktot_nonneg (s : BRel (ZIdx B)) : 0 ≤ S.Ktot s :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- The coefficient `C^{(M)}_d(s)` with the truncated means. -/
noncomputable def coefM (M d : ℕ) (s : BRel (ZIdx B)) : ℝ :=
  (∑ γ ∈ Finset.univ.filter (fun γ => S.D.deg γ = d), ∑ l : Fin (S.D.deg γ) → S.D.Lab,
    (S.D.κ γ s l : ℝ) * ∏ k, S.QJ ⟨γ, k, l k⟩ M) / (d.factorial : ℝ)

theorem tendsto_coefM (d : ℕ) (s : BRel (ZIdx B)) :
    Tendsto (fun M => S.coefM M d s) atTop (𝓝 (S.coef d s)) := by
  unfold coefM coef
  refine Tendsto.div_const (tendsto_finsetSum _ fun γ _ => tendsto_finsetSum _ fun l _ =>
    Tendsto.const_mul _ (tendsto_finsetProd _ fun k _ => S.tendsto_QJ _)) _

/-- Regrouping the sum of the coefficients: `Σ_{deg γ ≤ d₀} Σ_λ κ (ΠQ/deg!) N^{deg} = Σ_{d ≤ d₀} C_d N^d`. -/
theorem sum_regroup (d₀ : ℕ) (s : BRel (ZIdx B)) (X : ℝ) (Qf : S.Item → ℝ) :
    ∑ γ ∈ Finset.univ.filter (fun γ => S.D.deg γ ≤ d₀), ∑ l : Fin (S.D.deg γ) → S.D.Lab,
      (S.D.κ γ s l : ℝ) * ((∏ k, Qf ⟨γ, k, l k⟩) / ((S.D.deg γ).factorial : ℝ) * X ^ S.D.deg γ) =
    ∑ d ∈ Finset.range (d₀ + 1), (∑ γ ∈ Finset.univ.filter (fun γ => S.D.deg γ = d),
      ∑ l : Fin (S.D.deg γ) → S.D.Lab, (S.D.κ γ s l : ℝ) * ∏ k, Qf ⟨γ, k, l k⟩) / (d.factorial : ℝ) * X ^ d := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := S.D.deg) (t := Finset.range (d₀ + 1))
    (fun γ hγ => Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hγ).2; omega))]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.filter_filter]
  have e : (Finset.univ.filter (fun γ => S.D.deg γ ≤ d₀ ∧ S.D.deg γ = d)) =
      Finset.univ.filter (fun γ => S.D.deg γ = d) := by
    ext γ; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨by have := Finset.mem_range.mp hd; omega, h⟩
  rw [e, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun γ hγ => ?_)
  have hdeg := (Finset.mem_filter.mp hγ).2
  rw [Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [show ((S.D.deg γ).factorial : ℝ) = (d.factorial : ℝ) by rw [hdeg],
    show X ^ S.D.deg γ = X ^ d by rw [hdeg]]
  ring

/-! ## §3 The upper bound at the starting point (of the form of Proposition 12.27 (i)) -/

/-- `Ξ⁺` restricted to `p ≥ |u♯|`. -/
noncomputable def XiHat (i : S.Item) (ω : List (Fin 2)) (p : ℕ) : ℝ :=
  if S.us.length ≤ p then (S.XiJ i ω.length ω p : ℝ) else 0

theorem XiHat_nonneg (i : S.Item) (ω : List (Fin 2)) (p : ℕ) : 0 ≤ S.XiHat i ω p := by
  unfold XiHat; split_ifs <;> positivity

/-- `ε_j ≥ 0`. -/
theorem epsIter_nonneg {Bv η : ℝ} (hBv : 0 ≤ Bv) (hη : 0 ≤ η) (N : ℕ) : ∀ j, 0 ≤ W3a.epsIter Bv η N j
  | 0 => by simp [W3a.epsIter]
  | 1 => by simp [W3a.epsIter, hη]
  | j + 2 => by
    simp only [W3a.epsIter]
    have := epsIter_nonneg hBv hη N (j + 1)
    positivity

/-- The product and the length of the sequence of an iterated sum (`[ξ_{s-1}, …, ξ_0]`). -/
theorem ofFn_rev_prod {s : ℕ} (Qf : Fin s → ℝ) :
    ((List.ofFn (fun j : Fin s => ((fun _ : ℕ => (0 : ℝ)), Qf j.rev))).map Prod.snd).prod = ∏ k, Qf k := by
  rw [List.map_ofFn, List.prod_ofFn]
  exact Equiv.prod_comp Fin.revPerm Qf

/-- The upper bound for the iterated sum of a sequence that satisfies `IterHyp` (for one skeleton and one sequence of labels). -/
theorem tupSum_le_main {s : ℕ} {Bv η : ℝ} {N : ℕ} (hBv : 0 ≤ Bv) (hN : 1 ≤ N)
    (ξ : Fin s → ℕ → ℝ) (Qf : Fin s → ℝ) (h : ∀ k, W3a.IterHyp Bv η N (ξ k) (Qf k)) :
    tupSum s 1 N ξ ≤ (∏ k, Qf k) / (s.factorial : ℝ) * (N : ℝ) ^ s + W3a.epsIter Bv η N s * (N : ℝ) ^ s := by
  set L : List ((ℕ → ℝ) × ℝ) := List.ofFn (fun j : Fin s => (ξ j.rev, Qf j.rev))
  have hL : ∀ x ∈ L, W3a.IterHyp Bv η N x.1 x.2 := by
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact h j.rev
  have happ := W3a.iterSum_approx hBv hN L hL N le_rfl
  have e1 : W3a.isum (L.map Prod.fst) N = tupSum s 1 N ξ := by
    rw [← gsum_ofFn 1 s ξ N]
    unfold W3a.isum
    rw [List.map_map, List.map_ofFn]
    rfl
  have e2 : (L.map Prod.snd).prod = ∏ k, Qf k := by
    rw [List.map_ofFn, List.prod_ofFn]
    exact Equiv.prod_comp Fin.revPerm Qf
  have e3 : L.length = s := List.length_ofFn
  rw [e1, e2, e3] at happ
  have := (abs_le.mp happ).2
  linarith

/-- **The upper bound at the starting point** (of the form of Proposition 12.27 (i)). -/
theorem aval_le_of_iterHyp (m : List (Fin 2)) (d₀ : ℕ) (hdeg : ∀ d, d₀ < d → S.coef d (S.D.sT m) = 0)
    {Bv η : ℝ} (hBv : 0 ≤ Bv) (hη : 0 ≤ η)
    (hN : 1 ≤ (fullW S.us [] S.y'' S.z m S.R).length)
    (hI : ∀ i : S.Item, W3a.IterHyp Bv η (fullW S.us [] S.y'' S.z m S.R).length
      (S.XiHat i (fullW S.us [] S.y'' S.z m S.R)) (S.Qc i)) :
    (aval B (fullW S.us [] S.y'' S.z m S.R) : ℝ) ≤
      ∑ d ∈ Finset.range (d₀ + 1), S.coef d (S.D.sT m) * ((fullW S.us [] S.y'' S.z m S.R).length : ℝ) ^ d +
        S.Ktot (S.D.sT m) * (3 ^ S.Dm * (Bv + 1) ^ S.Dm * (η + 1 / (fullW S.us [] S.y'' S.z m S.R).length)) *
          ((fullW S.us [] S.y'' S.z m S.R).length : ℝ) ^ d₀ := by
  set ω := fullW S.us [] S.y'' S.z m S.R
  set N := ω.length
  set s := S.D.sT m
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set Eb : ℝ := 3 ^ S.Dm * (Bv + 1) ^ S.Dm * (η + 1 / N)
  have hEb : 0 ≤ Eb := by positivity
  -- the bound for each skeleton
  have hterm : ∀ γ, (S.D.term m γ : ℝ) ≤
      if S.D.deg γ ≤ d₀ then ∑ l : Fin (S.D.deg γ) → S.D.Lab, (S.D.κ γ s l : ℝ) *
        ((∏ k, S.Qc ⟨γ, k, l k⟩) / ((S.D.deg γ).factorial : ℝ) * (N : ℝ) ^ S.D.deg γ + Eb * (N : ℝ) ^ d₀)
      else 0 := by
    intro γ
    have h1 := termOf_le_upper1 B S.D.labS (S.D.deg γ) (S.D.κ γ) (S.D.g γ) (S.D.t0 γ) (S.D.t1abs m γ) s ω
    have h1r : (S.D.term m γ : ℝ) ≤ ∑ l : Fin (S.D.deg γ) → S.D.Lab, (S.D.κ γ s l : ℝ) *
        ∑ p ∈ incrSet (S.D.deg γ) (S.D.t0 γ) (S.D.t1abs m γ),
          ∏ k, ((XiP B S.D.labS (S.D.g γ k) (l k) ω (p k) : ℕ) : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr h1
      push_cast at this
      exact this
    refine le_trans h1r ?_
    -- the positions are at least `t₀ ≥ |u♯|`
    have hpos : ∀ l : Fin (S.D.deg γ) → S.D.Lab, ∑ p ∈ incrSet (S.D.deg γ) (S.D.t0 γ) (S.D.t1abs m γ),
        ∏ k, ((XiP B S.D.labS (S.D.g γ k) (l k) ω (p k) : ℕ) : ℝ) =
        ∑ p ∈ incrSet (S.D.deg γ) (S.D.t0 γ) (S.D.t1abs m γ), ∏ k, S.XiHat ⟨γ, k, l k⟩ ω (p k) := by
      intro l
      refine Finset.sum_congr rfl (fun p hp => Finset.prod_congr rfl (fun k _ => ?_))
      classical
      unfold incrSet at hp
      rw [Finset.mem_filter] at hp
      have hk : S.us.length ≤ p k := le_trans (S.hD γ) (hp.2.2 k)
      unfold XiHat
      simp only [hk, ↓reduceIte]
      rfl
    split_ifs with hd
    · refine Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
      rw [hpos l]
      have ht := incrSet_le_tupSum (t0 := S.D.t0 γ) (S.D.t1abs_le m γ) (fun k => S.XiHat ⟨γ, k, l k⟩ ω)
        (fun k p => S.XiHat_nonneg _ ω p)
      have hm := tupSum_le_main hBv hN (fun k => S.XiHat ⟨γ, k, l k⟩ ω) (fun k => S.Qc ⟨γ, k, l k⟩)
        (fun k => hI _)
      have he := W3a.epsIter_le hBv hη hN (S.D.deg γ)
      have hpow : (3 : ℝ) ^ S.D.deg γ * (Bv + 1) ^ S.D.deg γ ≤ 3 ^ S.Dm * (Bv + 1) ^ S.Dm := by
        have h3 : (3 : ℝ) ^ S.D.deg γ ≤ 3 ^ S.Dm := pow_le_pow_right₀ (by norm_num) (S.deg_le_Dm γ)
        have h4 : (Bv + 1) ^ S.D.deg γ ≤ (Bv + 1) ^ S.Dm := pow_le_pow_right₀ (by linarith) (S.deg_le_Dm γ)
        exact mul_le_mul h3 h4 (by positivity) (by positivity)
      have hηN : 0 ≤ η + 1 / (N : ℝ) := by positivity
      have he' : W3a.epsIter Bv η N (S.D.deg γ) ≤ Eb := by
        refine le_trans he ?_
        exact mul_le_mul_of_nonneg_right hpow hηN
      have hNp : (N : ℝ) ^ S.D.deg γ ≤ (N : ℝ) ^ d₀ := pow_le_pow_right₀ hNr hd
      have heN : W3a.epsIter Bv η N (S.D.deg γ) * (N : ℝ) ^ S.D.deg γ ≤ Eb * (N : ℝ) ^ d₀ := by
        have he0 : 0 ≤ W3a.epsIter Bv η N (S.D.deg γ) := epsIter_nonneg hBv hη N _
        exact mul_le_mul he' hNp (by positivity) hEb
      linarith [ht, hm]
    · -- the degree exceeds `d₀`: 0 by degeneration
      apply le_of_eq
      refine Finset.sum_eq_zero (fun l _ => ?_)
      rcases S.coef_zero_cases (hdeg (S.D.deg γ) (by omega)) γ rfl l with hk | ⟨k, hk⟩
      · rw [hk]; simp
      · rw [hpos l]
        refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun p hp => ?_))
        refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
        classical
        unfold incrSet at hp
        rw [Finset.mem_filter] at hp
        have hpk : S.us.length ≤ p k := le_trans (S.hD γ) (hp.2.2 k)
        unfold XiHat
        simp only [hpk, ↓reduceIte]
        norm_cast
        unfold XiJ
        refine Finset.sum_eq_zero (fun r hr => ?_)
        have hr1 := (Finset.mem_Icc.mp hr).1
        unfold xiI xiOf
        by_cases hlab : muZ B (ω.take (p k)) = S.D.labS (l k)
        · have hreach := S.reach_of_ge m hpk
          by_cases hlen : ((ω.drop (p k)).take r).length = r
          · have := S.degen ⟨γ, k, l k⟩ hk hreach hlab hr1 _ hlen
            simp only [gI] at this
            rw [this, mul_zero]
          · have : S.D.g γ k (l k) r ((ω.drop (p k)).take r) = 0 := by
              by_contra hne
              exact hlen (S.D.g_len γ k (l k) _ _ hne)
            rw [this, mul_zero]
        · unfold ind; simp [hlab]
  -- the total
  have hsum : (aval B ω : ℝ) = ∑ γ, (S.D.term m γ : ℝ) := by
    rw [S.D.aval_eq m]; push_cast; rfl
  rw [hsum]
  calc ∑ γ, (S.D.term m γ : ℝ)
      ≤ ∑ γ, (if S.D.deg γ ≤ d₀ then ∑ l : Fin (S.D.deg γ) → S.D.Lab, (S.D.κ γ s l : ℝ) *
          ((∏ k, S.Qc ⟨γ, k, l k⟩) / ((S.D.deg γ).factorial : ℝ) * (N : ℝ) ^ S.D.deg γ + Eb * (N : ℝ) ^ d₀)
          else 0) := Finset.sum_le_sum (fun γ _ => hterm γ)
    _ = ∑ γ ∈ Finset.univ.filter (fun γ => S.D.deg γ ≤ d₀), ∑ l : Fin (S.D.deg γ) → S.D.Lab,
          (S.D.κ γ s l : ℝ) * ((∏ k, S.Qc ⟨γ, k, l k⟩) / ((S.D.deg γ).factorial : ℝ) * (N : ℝ) ^ S.D.deg γ) +
        ∑ γ ∈ Finset.univ.filter (fun γ => S.D.deg γ ≤ d₀), ∑ l : Fin (S.D.deg γ) → S.D.Lab,
          (S.D.κ γ s l : ℝ) * (Eb * (N : ℝ) ^ d₀) := by
        rw [← Finset.sum_add_distrib, Finset.sum_filter]
        refine Finset.sum_congr rfl (fun γ _ => ?_)
        split_ifs
        · rw [← Finset.sum_add_distrib]; congr 1; funext l; ring
        · rfl
    _ ≤ _ := by
        rw [S.sum_regroup d₀ s N S.Qc]
        unfold coef
        refine add_le_add le_rfl ?_
        have hle : ∑ γ ∈ Finset.univ.filter (fun γ => S.D.deg γ ≤ d₀), ∑ l : Fin (S.D.deg γ) → S.D.Lab,
            (S.D.κ γ s l : ℝ) * (Eb * (N : ℝ) ^ d₀) ≤ S.Ktot s * (Eb * (N : ℝ) ^ d₀) := by
          calc ∑ γ ∈ Finset.univ.filter (fun γ => S.D.deg γ ≤ d₀), ∑ l : Fin (S.D.deg γ) → S.D.Lab,
                (S.D.κ γ s l : ℝ) * (Eb * (N : ℝ) ^ d₀)
              = ∑ γ ∈ Finset.univ.filter (fun γ => S.D.deg γ ≤ d₀),
                  (∑ l : Fin (S.D.deg γ) → S.D.Lab, (S.D.κ γ s l : ℝ)) * (Eb * (N : ℝ) ^ d₀) := by
                simp only [Finset.sum_mul]
            _ ≤ ∑ γ, (∑ l : Fin (S.D.deg γ) → S.D.Lab, (S.D.κ γ s l : ℝ)) * (Eb * (N : ℝ) ^ d₀) :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                  (fun γ _ _ => mul_nonneg (Finset.sum_nonneg fun l _ => Nat.cast_nonneg _) (by positivity))
            _ = S.Ktot s * (Eb * (N : ℝ) ^ d₀) := by rw [Ktot, Finset.sum_mul]
        calc _ ≤ S.Ktot s * (Eb * (N : ℝ) ^ d₀) := hle
          _ = _ := by simp only [Eb]; ring

/-! ## §4 The lower bound at the end point (of the form of Proposition 12.28 (i)) -/

/-- **The lower bound at the end point**: the part of degree `d`. The sequences `Ξ^{(M)}`, restricted to the good positions, satisfy `IterHyp`. -/
theorem aval_ge_of_iterHyp (m : List (Fin 2)) (d M : ℕ) (hM : 1 ≤ M) {Bv η B' : ℝ} (hBv : 0 ≤ Bv)
    (hη : 0 ≤ η) (hB'0 : 0 ≤ B') {N : ℕ} (hN : 1 ≤ N) (good : ℕ → Prop) [DecidablePred good]
    (hgood : ∀ p, good p → S.τ.length ≤ p ∧ p + M ≤ S.τ.length + m.length)
    (hI : ∀ i : S.Item, W3a.IterHyp Bv η N
      (fun p => if good p then (S.XiJ i M (fullW S.us [] S.y'' S.z m S.R) p : ℝ) else 0) (S.QJ i M))
    (hB' : ∀ i : S.Item, ∀ p, (S.XiJ i M (fullW S.us [] S.y'' S.z m S.R) p : ℝ) ≤ B') :
    S.coefM M d (S.D.sT m) * (N : ℝ) ^ d -
        S.Ktot (S.D.sT m) * (W3a.epsIter Bv η N d * (N : ℝ) ^ d +
          ((d - 1 : ℕ) : ℝ) * ((M - 1 : ℕ) : ℝ) * B' ^ d * (N : ℝ) ^ (d - 1)) ≤
      (aval B (fullW S.us [] S.y'' S.z m S.R) : ℝ) := by
  set ω := fullW S.us [] S.y'' S.z m S.R
  set s := S.D.sT m
  set err : ℝ := W3a.epsIter Bv η N d * (N : ℝ) ^ d +
    ((d - 1 : ℕ) : ℝ) * ((M - 1 : ℕ) : ℝ) * B' ^ d * (N : ℝ) ^ (d - 1)
  have herr : 0 ≤ err := by
    have := epsIter_nonneg hBv hη N d
    positivity
  -- the lower bound for each skeleton (in the form of degree `deg γ`)
  set errF : ℕ → ℝ := fun j => W3a.epsIter Bv η N j * (N : ℝ) ^ j +
    ((j - 1 : ℕ) : ℝ) * ((M - 1 : ℕ) : ℝ) * B' ^ j * (N : ℝ) ^ (j - 1) with herrF
  have hterm0 : ∀ γ, ∑ l : Fin (S.D.deg γ) → S.D.Lab, (S.D.κ γ s l : ℝ) *
        ((∏ k, S.QJ ⟨γ, k, l k⟩ M) / ((S.D.deg γ).factorial : ℝ) * (N : ℝ) ^ S.D.deg γ - errF (S.D.deg γ)) ≤
      (S.D.term m γ : ℝ) := by
    intro γ
    have h1 := S.D.lower_le_term m γ M
    have h1r : ∑ l : Fin (S.D.deg γ) → S.D.Lab, (S.D.κ γ s l : ℝ) *
        ∑ q ∈ gapSet (S.D.deg γ) (S.D.t0 γ) (S.D.t1abs m γ) M,
          ∏ k, ((XiLe B S.D.labS (S.D.g γ k) (l k) M ω (q k) : ℕ) : ℝ) ≤ (S.D.term m γ : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr h1
      push_cast at this
      exact this
    refine le_trans ?_ h1r
    refine Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    set f' : Fin (S.D.deg γ) → ℕ → ℝ := fun k p =>
      if good p then (S.XiJ ⟨γ, k, l k⟩ M ω p : ℝ) else 0
    have hgap := tupSum_le_gapSet (s := S.D.deg γ) (t0 := S.D.t0 γ) (t1 := S.D.t1abs m γ) (n := N) hM
      (fun k p => ((XiLe B S.D.labS (S.D.g γ k) (l k) M ω p : ℕ) : ℝ)) f'
      (fun k p => Nat.cast_nonneg _) (fun k p => by simp only [f']; split_ifs <;> positivity)
      (fun k p => by simp only [f']; split_ifs <;> simp [XiJ_eq_XiLe])
      (fun k p hp => by
        simp only [f'] at hp
        split_ifs at hp with hg
        · obtain ⟨h1, h2⟩ := hgood p hg
          refine ⟨le_trans (S.D.t0_le γ) (by rw [S.topW_eq]; exact h1), ?_⟩
          unfold DecompData.t1abs
          rw [S.topW_eq]
          omega
        · exact absurd rfl hp)
    set L : List (((ℕ → ℝ) × ℕ) × ℝ) :=
      List.ofFn (fun j : Fin (S.D.deg γ) => ((f' j.rev, M), S.QJ ⟨γ, j.rev, l j.rev⟩ M))
    have hL : ∀ x ∈ L, W3a.IterHyp Bv η N x.1.1 x.2 ∧ (∀ p, x.1.1 p ≤ B') ∧ 1 ≤ x.1.2 ∧ x.1.2 ≤ M := by
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      refine ⟨hI _, fun p => ?_, hM, le_rfl⟩
      simp only [f']; split_ifs
      · exact hB' _ p
      · exact hB'0
    have happ := (W3a.gsum_approx hBv hN hM L hL N le_rfl).2
    have e1 : L.map Prod.fst = List.ofFn (fun j : Fin (S.D.deg γ) => (f' j.rev, M)) := by
      rw [List.map_ofFn]; rfl
    have e2 : (L.map Prod.snd).prod = ∏ k, S.QJ ⟨γ, k, l k⟩ M := by
      rw [List.map_ofFn, List.prod_ofFn]
      exact Equiv.prod_comp Fin.revPerm (fun k => S.QJ ⟨γ, k, l k⟩ M)
    have e3 : L.length = S.D.deg γ := List.length_ofFn
    rw [e1, gsum_ofFn M (S.D.deg γ) f' N, e2, e3] at happ
    have := le_trans happ hgap
    simp only [herrF]
    linarith
  have hterm : ∀ γ, S.D.deg γ = d →
      ∑ l : Fin (S.D.deg γ) → S.D.Lab, (S.D.κ γ s l : ℝ) *
        ((∏ k, S.QJ ⟨γ, k, l k⟩ M) / (d.factorial : ℝ) * (N : ℝ) ^ d - err) ≤ (S.D.term m γ : ℝ) := by
    intro γ hd
    have := hterm0 γ
    simp only [hd] at this
    simpa [herrF, err] using this
  -- the total
  have hsum : (aval B ω : ℝ) = ∑ γ, (S.D.term m γ : ℝ) := by
    rw [S.D.aval_eq m]; push_cast; rfl
  rw [hsum]
  calc S.coefM M d s * (N : ℝ) ^ d - S.Ktot s * err
      ≤ ∑ γ ∈ Finset.univ.filter (fun γ => S.D.deg γ = d), ∑ l : Fin (S.D.deg γ) → S.D.Lab,
          (S.D.κ γ s l : ℝ) * ((∏ k, S.QJ ⟨γ, k, l k⟩ M) / (d.factorial : ℝ) * (N : ℝ) ^ d - err) := by
        have hK : ∑ γ ∈ Finset.univ.filter (fun γ => S.D.deg γ = d), ∑ l : Fin (S.D.deg γ) → S.D.Lab,
            (S.D.κ γ s l : ℝ) ≤ S.Ktot s := by
          unfold Ktot
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun γ _ _ => Finset.sum_nonneg fun l _ => Nat.cast_nonneg _)
        have e : ∑ γ ∈ Finset.univ.filter (fun γ => S.D.deg γ = d), ∑ l : Fin (S.D.deg γ) → S.D.Lab,
            (S.D.κ γ s l : ℝ) * ((∏ k, S.QJ ⟨γ, k, l k⟩ M) / (d.factorial : ℝ) * (N : ℝ) ^ d - err) =
            S.coefM M d s * (N : ℝ) ^ d - (∑ γ ∈ Finset.univ.filter (fun γ => S.D.deg γ = d),
              ∑ l : Fin (S.D.deg γ) → S.D.Lab, (S.D.κ γ s l : ℝ)) * err := by
          unfold coefM
          rw [Finset.sum_div, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun γ _ => ?_)
          rw [Finset.sum_div, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          ring
        rw [e]
        nlinarith
    _ ≤ ∑ γ ∈ Finset.univ.filter (fun γ => S.D.deg γ = d), (S.D.term m γ : ℝ) :=
        Finset.sum_le_sum (fun γ hγ => hterm γ (Finset.mem_filter.mp hγ).2)
    _ ≤ ∑ γ, (S.D.term m γ : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun γ _ _ => Nat.cast_nonneg _)

end Setup

end Collatz.Arctic.NatQ5.W3h
