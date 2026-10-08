/-
# The pivot basis: the image cone of a non-negative idempotent is simplicial (used in the proof of Lemma D.4)

The statement: let `P` be a non-negative real matrix with `P² = P` and rank `r`,
`V := P ℝ^K` and `𝒞 := P ℝ^K_{≥0}`. Then `𝒞 = V ∩ ℝ^K_{≥0}`, `𝒞` has exactly `r` extreme rays, their generators are linearly independent, and
`𝒞` is the cone they generate (a simplicial cone).

The Lean form (`exists_pivot_basis`, `PivotBasis.inCone_iff`, `inCone_iff_image`, `PivotBasis.isRay_iff`, `PivotBasis.rank_eq`): there are `r`, **pivots** `k : Fin r → K` and non-negative
vectors `f : Fin r → (K → ℝ)` such that
* `P f_i = f_i`, `f_i(k_j) = δ_{ij}` (so `f` is linearly independent), `P_{k_i k_i} > 0`,
* if `P v = v`, then `v = Σ_i v(k_i) f_i` (the coordinates in `V` are the values at the pivots),
* `𝒞 = {Σ β_i f_i : β ≥ 0}` and `r = rank P`,
* the elements of `𝒞` with minimal support (`IsRay`) are exactly the positive multiples of the `f_i`.

An earlier argument is phrased with extreme rays; here it is phrased with **minimal supports** (`IsRay`: the only elements of the cone with support inside the support are multiples).
That elements of minimal support generate the extreme rays of a cone in the non-negative orthant is classical, and `isRay_iff` is its Lean form
(the general theory of extreme rays is not used). The proof is elementary: subtraction at the minimal ratio on the support (`sub_min_ratio`), induction on the size of the support,
existence of pivots (`ray_pivot`: each term of `f = Σ_k f(k) P e_k` is a multiple of `f`), and the pivot of one support lies outside a different support (`ray_pivot_disjoint`).
-/
import Mathlib

namespace Collatz.Arctic.NatQ5.Rigid

open Matrix

set_option linter.unusedSectionVars false

variable {K : Type*} [Fintype K] [DecidableEq K]

/-! ## §1 Supports and the cone -/

/-- The support: the non-zero coordinates. -/
noncomputable def supp (v : K → ℝ) : Finset K := Finset.univ.filter fun i => v i ≠ 0

theorem mem_supp {v : K → ℝ} {i : K} : i ∈ supp v ↔ v i ≠ 0 := by simp [supp]

theorem supp_smul {t : ℝ} (ht : t ≠ 0) (v : K → ℝ) : supp (t • v) = supp v := by
  ext i; simp [supp, ht]

theorem supp_eq_empty {v : K → ℝ} : supp v = ∅ ↔ v = 0 := by
  constructor
  · intro h; funext i; by_contra hi
    have : i ∈ supp v := mem_supp.mpr hi
    rw [h] at this; simp at this
  · rintro rfl; ext i; simp [supp]

theorem supp_nonempty {v : K → ℝ} (h : v ≠ 0) : (supp v).Nonempty :=
  Finset.nonempty_iff_ne_empty.mpr fun he => h (supp_eq_empty.mp he)

variable (P : Matrix K K ℝ)

theorem mulVec_apply' (v : K → ℝ) (i : K) : (P *ᵥ v) i = ∑ j, P i j * v j := rfl

/-- An element of the cone `𝒞 = V ∩ ℝ^K_{≥0}`: non-negative with `P v = v`. -/
def InCone (v : K → ℝ) : Prop := (∀ i, 0 ≤ v i) ∧ P *ᵥ v = v

/-- An element of the cone with minimal support (the only elements of the cone with support inside its support are its multiples). -/
def IsRay (v : K → ℝ) : Prop :=
  InCone P v ∧ v ≠ 0 ∧ ∀ w, InCone P w → supp w ⊆ supp v → ∃ t : ℝ, w = t • v

/-- The `k`th column of `P`. -/
def pcol (k : K) : K → ℝ := fun i => P i k

variable {P}

section Idem

variable (hP0 : ∀ i j, 0 ≤ P i j) (hPP : P * P = P)
include hP0 hPP

theorem pcol_inCone (k : K) : InCone P (pcol P k) := by
  refine ⟨fun i => hP0 i k, ?_⟩
  funext i
  rw [mulVec_apply']
  have := congrFun (congrFun hPP i) k
  rw [Matrix.mul_apply] at this
  exact this

omit hP0 hPP in
/-- If `P v = v`, then `v = Σ_k v(k) P e_k`. -/
theorem expand_fixed {v : K → ℝ} (hv : P *ᵥ v = v) : v = ∑ k, v k • pcol P k := by
  funext i
  conv_lhs => rw [← hv]
  rw [mulVec_apply', Finset.sum_apply]
  exact Finset.sum_congr rfl fun k _ => by simp [pcol, mul_comm]

omit hPP in
/-- If `v ∈ 𝒞` and `v(k) ≠ 0`, then `supp(P e_k) ⊆ supp v`. -/
theorem supp_pcol_subset {v : K → ℝ} (hv : InCone P v) {k : K} (hk : v k ≠ 0) :
    supp (pcol P k) ⊆ supp v := by
  intro i hi
  rw [mem_supp] at hi ⊢
  have hvk : 0 < v k := lt_of_le_of_ne (hv.1 k) (Ne.symm hk)
  have hPik : 0 < P i k := lt_of_le_of_ne (hP0 i k) (Ne.symm hi)
  have h1 : v i = ∑ j, P i j * v j := by rw [← mulVec_apply', hv.2]
  have h2 : P i k * v k ≤ ∑ j, P i j * v j :=
    Finset.single_le_sum (f := fun j => P i j * v j) (fun j _ => mul_nonneg (hP0 i j) (hv.1 j))
      (Finset.mem_univ k)
  have : 0 < v i := by rw [h1]; exact lt_of_lt_of_le (mul_pos hPik hvk) h2
  exact this.ne'

end Idem

omit [DecidableEq K] in
theorem InCone.sub_smul {a b : K → ℝ} (ha : P *ᵥ a = a) (hb : P *ᵥ b = b) (t : ℝ) :
    P *ᵥ (a - t • b) = a - t • b := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, ha, hb]

/-- Subtraction at the minimal ratio on the support: if `a, b ∈ 𝒞` and `b ≠ 0`, there are `t ≥ 0` and `i ∈ supp b` with `a - t b ∈ 𝒞` and `(a - t b)(i) = 0`. -/
theorem sub_min_ratio {a b : K → ℝ} (ha : InCone P a) (hb : InCone P b) (hb0 : b ≠ 0) :
    ∃ t : ℝ, 0 ≤ t ∧ ∃ i ∈ supp b, InCone P (a - t • b) ∧ (a - t • b) i = 0 := by
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image (supp b) (fun j => a j / b j) (supp_nonempty hb0)
  have hbi : 0 < b i := lt_of_le_of_ne (hb.1 i) (Ne.symm (mem_supp.mp hi))
  refine ⟨a i / b i, div_nonneg (ha.1 i) hbi.le, i, hi, ⟨fun j => ?_, InCone.sub_smul ha.2 hb.2 _⟩, ?_⟩
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_nonneg]
    by_cases hj : j ∈ supp b
    · have hbj : 0 < b j := lt_of_le_of_ne (hb.1 j) (Ne.symm (mem_supp.mp hj))
      have := hmin j hj
      rw [div_le_div_iff₀ hbi hbj] at this
      rw [div_mul_eq_mul_div, div_le_iff₀ hbi]
      linarith
    · have : b j = 0 := by simpa [mem_supp] using hj
      rw [this, mul_zero]; exact ha.1 j
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

/-! ## §2 Existence of minimal elements, pivots, distinct supports -/

/-- Within the support of a non-zero element of the cone there is a minimal element. -/
theorem exists_ray_le {v : K → ℝ} (hv : InCone P v) (hv0 : v ≠ 0) :
    ∃ ρ, IsRay P ρ ∧ supp ρ ⊆ supp v := by
  induction hn : (supp v).card using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    by_cases hr : IsRay P v
    · exact ⟨v, hr, le_rfl⟩
    · have : ∃ w, InCone P w ∧ supp w ⊆ supp v ∧ ∀ t : ℝ, w ≠ t • v := by
        by_contra hc
        apply hr
        refine ⟨hv, hv0, fun w hw hws => ?_⟩
        by_contra hne
        push Not at hne
        exact hc ⟨w, hw, hws, hne⟩
      obtain ⟨w, hw, hws, hwne⟩ := this
      obtain ⟨t, -, i, hi, hu, hui⟩ := sub_min_ratio hw hv hv0
      have hu0 : w - t • v ≠ 0 := fun h => hwne t (sub_eq_zero.mp h)
      have hsub : supp (w - t • v) ⊆ supp v := by
        intro j hj
        rw [mem_supp] at hj ⊢
        intro hvj
        apply hj
        have : w j = 0 := by
          by_contra hwj; exact (mem_supp.mp (hws (mem_supp.mpr hwj))) hvj
        simp [this, hvj]
      have hlt : (supp (w - t • v)).card < n := by
        rw [← hn]
        refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun he => ?_⟩)
        have : i ∈ supp (w - t • v) := he ▸ hi
        exact (mem_supp.mp this) hui
      obtain ⟨ρ, hρ, hρs⟩ := ih _ hlt hu hu0 rfl
      exact ⟨ρ, hρ, hρs.trans hsub⟩

section Idem2

variable (hP0 : ∀ i j, 0 ≤ P i j) (hPP : P * P = P)
include hP0 hPP

/-- **Pivots**: a minimal element `f` has `k` with `f(k) ≠ 0` and `P e_k = α f` (`α > 0`). -/
theorem ray_pivot {f : K → ℝ} (hf : IsRay P f) :
    ∃ k, f k ≠ 0 ∧ ∃ α : ℝ, 0 < α ∧ pcol P k = α • f := by
  have hex : ∀ k, ∃ α : ℝ, f k ≠ 0 → pcol P k = α • f := by
    intro k
    by_cases hk : f k = 0
    · exact ⟨0, fun h => absurd hk h⟩
    · obtain ⟨α, hα⟩ := hf.2.2 _ (pcol_inCone hP0 hPP k) (supp_pcol_subset hP0 hf.1 hk)
      exact ⟨α, fun _ => hα⟩
  choose α hα using hex
  have hsum : f = (∑ k, f k * α k) • f := by
    conv_lhs => rw [expand_fixed hf.1.2]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : f k = 0
    · simp [hk]
    · rw [hα k hk, smul_smul]
  have hs1 : ∑ k, f k * α k = 1 := by
    by_contra hne
    have : (1 - ∑ k, f k * α k) • f = 0 := by rw [sub_smul, one_smul, ← hsum, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exact hne (by linarith)
    · exact hf.2.1 h
  have : ∃ k, 0 < f k * α k := by
    by_contra hc
    push Not at hc
    have : ∑ k, f k * α k ≤ 0 := Finset.sum_nonpos fun k _ => hc k
    linarith
  obtain ⟨k, hk⟩ := this
  have hfk : 0 < f k := by
    rcases lt_or_eq_of_le (hf.1.1 k) with h | h
    · exact h
    · rw [← h, zero_mul] at hk; exact absurd hk (lt_irrefl 0)
  refine ⟨k, hfk.ne', α k, pos_of_mul_pos_right hk hfk.le, hα k hfk.ne'⟩

/-- Minimal elements with distinct supports: at the pivot `k` of `f`, the value of `f'` is 0. -/
theorem ray_pivot_disjoint {f f' : K → ℝ} (hf : IsRay P f) (hf' : IsRay P f')
    (hne : supp f ≠ supp f') {k : K} {α : ℝ} (hα : 0 < α) (hk : pcol P k = α • f) : f' k = 0 := by
  by_contra hfk
  have h1 : supp (pcol P k) ⊆ supp f' := supp_pcol_subset hP0 hf'.1 hfk
  rw [hk, supp_smul hα.ne'] at h1
  obtain ⟨t, ht⟩ := hf'.2.2 f hf.1 h1
  have ht0 : t ≠ 0 := by
    rintro rfl; exact hf.2.1 (by simpa using ht)
  exact hne (by rw [ht, supp_smul ht0])

end Idem2

/-! ## §3 The pivot basis -/

theorem IsRay.smul {f : K → ℝ} (hf : IsRay P f) {c : ℝ} (hc : 0 < c) : IsRay P (c • f) := by
  refine ⟨⟨fun i => mul_nonneg hc.le (hf.1.1 i), by rw [Matrix.mulVec_smul, hf.1.2]⟩,
    smul_ne_zero hc.ne' hf.2.1, fun w hw hws => ?_⟩
  rw [supp_smul hc.ne'] at hws
  obtain ⟨t, ht⟩ := hf.2.2 w hw hws
  exact ⟨t / c, by rw [ht, smul_smul, div_mul_cancel₀ _ hc.ne']⟩

/-- **The pivot basis**. -/
theorem exists_pivot_basis (hP0 : ∀ i j, 0 ≤ P i j) (hPP : P * P = P) :
    ∃ (r : ℕ) (k : Fin r → K) (f : Fin r → K → ℝ),
      (∀ i, InCone P (f i)) ∧ (∀ i, IsRay P (f i)) ∧
      (∀ i j, f i (k j) = if i = j then 1 else 0) ∧
      (∀ v, P *ᵥ v = v → v = ∑ i, v (k i) • f i) ∧
      (∀ i, 0 < P (k i) (k i)) := by
  classical
  -- Index by the family of supports of minimal elements.
  set Ss : Finset (Finset K) := Finset.univ.filter fun S => ∃ f, IsRay P f ∧ supp f = S with hSs
  have hmem : ∀ S : Ss, ∃ f, IsRay P f ∧ supp f = S.1 := fun S => (Finset.mem_filter.mp S.2).2
  choose ρ hρ hρs using hmem
  have hpiv : ∀ S : Ss, ∃ k, ρ S k ≠ 0 ∧ ∃ α : ℝ, 0 < α ∧ pcol P k = α • ρ S :=
    fun S => ray_pivot hP0 hPP (hρ S)
  choose kk hkk α hα hkα using hpiv
  -- Normalize: 1 at the pivot.
  have hρk : ∀ S, 0 < ρ S (kk S) := fun S => lt_of_le_of_ne ((hρ S).1.1 _) (Ne.symm (hkk S))
  set ff : Ss → K → ℝ := fun S => (ρ S (kk S))⁻¹ • ρ S with hff
  have hffray : ∀ S, IsRay P (ff S) := fun S => (hρ S).smul (inv_pos.mpr (hρk S))
  have hffsupp : ∀ S, supp (ff S) = S.1 := fun S => by
    rw [hff, supp_smul (inv_ne_zero (hρk S).ne'), hρs]
  have hdelta : ∀ S S', ff S (kk S') = if S = S' then 1 else 0 := by
    intro S S'
    by_cases h : S = S'
    · subst h; simp [hff, (hρk S).ne']
    · simp only [h, ↓reduceIte]
      have hne : supp (ff S) ≠ supp (ρ S') := by
        rw [hffsupp, hρs]; exact fun e => h (Subtype.ext e)
      exact ray_pivot_disjoint hP0 hPP (hρ S') (hffray S) hne.symm (hα S') (hkα S')
  -- Elements of the cone are linear combinations of `ff`.
  have hspan : ∀ v, InCone P v → ∃ β : Ss → ℝ, v = ∑ S, β S • ff S := by
    intro v hv
    induction hn : (supp v).card using Nat.strong_induction_on generalizing v with
    | _ n ih =>
      by_cases hv0 : v = 0
      · exact ⟨0, by simp [hv0]⟩
      obtain ⟨σ, hσ, hσs⟩ := exists_ray_le hv hv0
      have hSmem : supp σ ∈ Ss := Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ, hσ, rfl⟩
      set S : Ss := ⟨supp σ, hSmem⟩
      obtain ⟨s, hs⟩ := (hffray S).2.2 σ hσ.1 (by rw [hffsupp])
      obtain ⟨t, -, i, hi, hu, hui⟩ := sub_min_ratio hv hσ.1 hσ.2.1
      have hsub : supp (v - t • σ) ⊆ supp v := by
        intro j hj
        rw [mem_supp] at hj ⊢
        intro hvj
        apply hj
        have : σ j = 0 := by
          by_contra hσj; exact (mem_supp.mp (hσs (mem_supp.mpr hσj))) hvj
        simp [this, hvj]
      have hlt : (supp (v - t • σ)).card < n := by
        rw [← hn]
        refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun he => ?_⟩)
        have : i ∈ supp (v - t • σ) := he ▸ hσs hi
        exact (mem_supp.mp this) hui
      obtain ⟨β, hβ⟩ := ih _ hlt _ hu rfl
      refine ⟨fun S' => β S' + if S' = S then t * s else 0, ?_⟩
      have hsplit : ∑ S', (β S' + if S' = S then t * s else 0) • ff S' =
          (∑ S', β S' • ff S') + (t * s) • ff S := by
        simp only [add_smul, Finset.sum_add_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true]
      rw [hsplit, ← hβ, ← smul_smul, ← hs]
      abel
  -- Read the values at the pivots.
  have heval : ∀ β : Ss → ℝ, ∀ S', (∑ S, β S • ff S) (kk S') = β S' := by
    intro β S'
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, hdelta, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  have hfix : ∀ v, P *ᵥ v = v → v = ∑ S, v (kk S) • ff S := by
    intro v hv
    have hcol : ∀ k, ∃ β : Ss → ℝ, pcol P k = ∑ S, β S • ff S := fun k => hspan _ (pcol_inCone hP0 hPP k)
    choose β hβ using hcol
    have h1 : v = ∑ S, (∑ k, v k * β k S) • ff S := by
      conv_lhs => rw [expand_fixed hv]
      simp_rw [hβ, Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
    have h2 : ∀ S', v (kk S') = ∑ k, v k * β k S' := by
      intro S'; conv_lhs => rw [h1]
      exact heval _ S'
    conv_lhs => rw [h1]
    simp_rw [h2]
  -- Transfer to `Fin r`.
  set e := (Fintype.equivFin Ss).symm
  refine ⟨Fintype.card Ss, fun i => kk (e i), fun i => ff (e i), fun i => (hffray _).1,
    fun i => hffray _, fun i j => ?_, fun v hv => ?_, fun i => ?_⟩
  · show ff (e i) (kk (e j)) = _
    rw [hdelta]; simp [e.injective.eq_iff]
  · show v = ∑ i, v (kk (e i)) • ff (e i)
    conv_lhs => rw [hfix v hv]
    exact (e.sum_comp (fun S => v (kk S) • ff S)).symm
  · have h := congrFun (hkα (e i)) (kk (e i))
    simp only [pcol, Pi.smul_apply, smul_eq_mul] at h
    rw [h]
    exact mul_pos (hα _) (hρk _)

/-! ## §4 The data of the pivot basis, and the individual statements -/

/-- The data of a pivot basis (the conclusion of `exists_pivot_basis`, bundled). -/
structure PivotBasis (P : Matrix K K ℝ) where
  r : ℕ
  k : Fin r → K
  f : Fin r → K → ℝ
  inCone : ∀ i, InCone P (f i)
  ray : ∀ i, IsRay P (f i)
  delta : ∀ i j, f i (k j) = if i = j then 1 else 0
  expand : ∀ v, P *ᵥ v = v → v = ∑ i, v (k i) • f i
  diag_pos : ∀ i, 0 < P (k i) (k i)

theorem nonempty_pivotBasis (hP0 : ∀ i j, 0 ≤ P i j) (hPP : P * P = P) : Nonempty (PivotBasis P) := by
  obtain ⟨r, k, f, h1, h2, h3, h4, h5⟩ := exists_pivot_basis hP0 hPP
  exact ⟨⟨r, k, f, h1, h2, h3, h4, h5⟩⟩

namespace PivotBasis

variable (B : PivotBasis P)

theorem eval_sum (β : Fin B.r → ℝ) (j : Fin B.r) : (∑ i, β i • B.f i) (B.k j) = β j := by
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, B.delta, mul_ite, mul_one, mul_zero]
  simp

/-- The generators are linearly independent. -/
theorem linearIndependent : LinearIndependent ℝ B.f := by
  rw [Fintype.linearIndependent_iff]
  intro β hβ j
  have := B.eval_sum β j
  rw [hβ] at this
  simpa using this.symm

/-- `𝒞 = V ∩ ℝ^K_{≥0}` is the set of non-negative combinations of the generators (a simplicial cone). -/
theorem inCone_iff (v : K → ℝ) :
    InCone P v ↔ ∃ β : Fin B.r → ℝ, (∀ i, 0 ≤ β i) ∧ v = ∑ i, β i • B.f i := by
  constructor
  · intro hv
    exact ⟨fun i => v (B.k i), fun i => hv.1 _, B.expand v hv.2⟩
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨fun j => ?_, ?_⟩
    · rw [Finset.sum_apply]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hβ i) ((B.inCone i).1 j)
    · rw [Matrix.mulVec_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Matrix.mulVec_smul, (B.inCone i).2]

/-- The elements of minimal support are exactly the positive multiples of the generators. -/
theorem isRay_iff (v : K → ℝ) : IsRay P v ↔ ∃ i, ∃ t : ℝ, 0 < t ∧ v = t • B.f i := by
  constructor
  · intro hv
    have hexp := B.expand v hv.1.2
    have : ∃ i, v (B.k i) ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hv.2.1
      rw [hexp]
      simp [hc]
    obtain ⟨i, hi⟩ := this
    have hvi : 0 < v (B.k i) := lt_of_le_of_ne (hv.1.1 _) (Ne.symm hi)
    have hsub : supp (B.f i) ⊆ supp v := by
      intro j hj
      rw [mem_supp] at hj ⊢
      have hfj : 0 < B.f i j := lt_of_le_of_ne ((B.inCone i).1 j) (Ne.symm hj)
      have h1 : v (B.k i) * B.f i j ≤ v j := by
        conv_rhs => rw [hexp]
        rw [Finset.sum_apply]
        exact Finset.single_le_sum (f := fun i' => (v (B.k i') • B.f i') j)
          (fun i' _ => mul_nonneg (hv.1.1 _) ((B.inCone i').1 j)) (Finset.mem_univ i)
      exact (lt_of_lt_of_le (mul_pos hvi hfj) h1).ne'
    obtain ⟨t, ht⟩ := hv.2.2 _ (B.inCone i) hsub
    have hti : t * v (B.k i) = 1 := by
      have := congrFun ht (B.k i)
      rw [B.delta, ite_eq_left_iff.mpr (fun h => absurd rfl h)] at this
      simpa [mul_comm] using this.symm
    have htpos : 0 < t := by
      by_contra hc
      push Not at hc
      nlinarith
    refine ⟨i, t⁻¹, inv_pos.mpr htpos, ?_⟩
    rw [ht, smul_smul, inv_mul_cancel₀ htpos.ne', one_smul]
  · rintro ⟨i, t, ht, rfl⟩
    exact (B.ray i).smul ht

/-- `r = rank P`. -/
theorem rank_eq (hPP : P * P = P) : P.rank = B.r := by
  have hrange : LinearMap.range P.mulVecLin = Submodule.span ℝ (Set.range B.f) := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      have hfix : P *ᵥ (P *ᵥ z) = P *ᵥ z := by rw [Matrix.mulVec_mulVec, hPP]
      rw [Matrix.mulVecLin_apply, B.expand _ hfix]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨B.f i, by rw [Matrix.mulVecLin_apply, (B.inCone i).2]⟩
  rw [Matrix.rank, hrange, finrank_span_eq_card B.linearIndependent, Fintype.card_fin]

end PivotBasis

/-- `𝒞 = P ℝ^K_{≥0}` (the first statement). -/
theorem inCone_iff_image (hP0 : ∀ i j, 0 ≤ P i j) (hPP : P * P = P) (v : K → ℝ) :
    InCone P v ↔ ∃ z : K → ℝ, (∀ i, 0 ≤ z i) ∧ v = P *ᵥ z := by
  constructor
  · intro hv; exact ⟨v, hv.1, hv.2.symm⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨fun i => ?_, by rw [Matrix.mulVec_mulVec, hPP]⟩
    rw [mulVec_apply']
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hP0 i j) (hz j)

end Collatz.Arctic.NatQ5.Rigid
