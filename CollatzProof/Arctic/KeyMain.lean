/-
Probabilistic ingredients (part 1) of Theorem B.7 (KEY) in the swap argument.

* `km_sum_append`, `km_sum_cons`, `km_wt_*`: weighted sums over block choices (values in an arbitrary type; used with `ℝ`).
* `km_swap_avg`: **step (a) of the proof of Theorem B.7** (averaging over the swap choices). `L ↦ L^e` is a weight-preserving bijection, so the weighted sum
  equals the uniform average over the swap choices `e`.
* Properties of `keyLaw` (`KeyDefs.lean`, the law of `z₀ + Σ_j e_j a_j` for uniform `e`): `km_law_nonneg`, `km_law_le_one`,
  `km_law_sum` (a probability measure), `km_law_shift`, `km_Q_shift` (the invariance of `Q_λ` under translations in **(Q1)**),
  `km_Q_nonneg`, `km_Q_le` (the crude bound `Q_λ ≤ 2^V λ^2` instead of `Q_λ ≤ λ`; it suffices because the Doeblin term is made arbitrarily
  small in the assembly).
* `km_cell`: **the cell formula**. From `ρ(e) < 2^V` and `(ρ(e) : ZMod 2^V) = z₀ + Σ_j e_j a_j`, the measure under `keyLaw` of the cell `C_u` is
  the proportion of `e` for which the top `ℓ` digits of `ρ(e)` are `u` (the content of `Pr(U = u) = E_β μ_β(C_u)` in step (a) of the proof of Theorem B.7).
-/
import CollatzProof.Arctic.KeyTerras2
import CollatzProof.Arctic.KeyDefs
import CollatzProof.Arctic.FamilyExp

namespace Collatz.Arctic

open Finset

/-! ### Sums over block choices -/

/-- Split a sum over block choices of length `a + m` into a double sum over the first `a` blocks and the remaining `m` blocks (arbitrary values). -/
theorem km_sum_append {M : Type*} [AddCommMonoid M] (a m : ℕ) (g : List Bool → M) :
    ∑ β ∈ blockChoices (a + m), g β = ∑ β₁ ∈ blockChoices a, ∑ β₂ ∈ blockChoices m, g (β₁ ++ β₂) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun β => (β.take a, β.drop a)) (fun p => p.1 ++ p.2) ?_ ?_ ?_ ?_ ?_
  · intro β hβ
    rw [fam_mem_blockChoices] at hβ
    simp only [Finset.mem_product, fam_mem_blockChoices, List.length_take, List.length_drop]
    omega
  · intro p hp
    simp only [Finset.mem_product, fam_mem_blockChoices] at hp
    rw [fam_mem_blockChoices, List.length_append, hp.1, hp.2]
  · intro β _
    exact List.take_append_drop a β
  · intro p hp
    simp only [Finset.mem_product, fam_mem_blockChoices] at hp
    obtain ⟨p1, p2⟩ := p
    simp only at hp ⊢
    rw [← hp.1, List.take_left, List.drop_left]
  · intro β _
    rw [List.take_append_drop]

/-- Split a sum of length `k + 1` at the first block (arbitrary values). -/
theorem km_sum_cons {M : Type*} [AddCommMonoid M] (k : ℕ) (f : List Bool → M) :
    ∑ β ∈ blockChoices (k + 1), f β
      = ∑ β ∈ blockChoices k, f (true :: β) + ∑ β ∈ blockChoices k, f (false :: β) := by
  rw [fam_blockChoices_succ, Finset.sum_union, Finset.sum_image, Finset.sum_image]
  · intro a _ b _ h; exact List.cons_injective h
  · intro a _ b _ h; exact List.cons_injective h
  · rw [Finset.disjoint_left]
    intro β h1 h2
    simp only [Finset.mem_image] at h1 h2
    obtain ⟨a, _, rfl⟩ := h1
    obtain ⟨b, _, h⟩ := h2
    simp at h

lemma km_wt_append (β₁ β₂ : List Bool) : wtβ (β₁ ++ β₂) = wtβ β₁ * wtβ β₂ := by
  simp [wtβ, List.map_append, List.prod_append]

lemma km_wt_nonneg (β : List Bool) : (0 : ℝ) ≤ (wtβ β : ℝ) := by
  exact_mod_cast fam_wt_nonneg β

lemma km_wt_sum (k : ℕ) : ∑ β ∈ blockChoices k, (wtβ β : ℝ) = 1 := by
  exact_mod_cast (fam_moments k).1

/-- The weighted double sum: `Σ_{β₁ β₂} w(β₁) w(β₂) = 1`. -/
lemma km_wt_sum2 (a m : ℕ) :
    ∑ β₁ ∈ blockChoices a, ∑ β₂ ∈ blockChoices m, (wtβ β₁ : ℝ) * (wtβ β₂ : ℝ) = 1 := by
  simp_rw [← Finset.mul_sum, km_wt_sum, mul_one]
  exact km_wt_sum a

/-- **Step (a) of the proof of Theorem B.7** (averaging over the swap choices): the swap `L ↦ L^e` is a weight-preserving bijection, so the weighted sum
equals the average over the swap choices `e`. -/
theorem km_swap_avg (I n : ℕ) (G : List Bool → ℝ) :
    ∑ L ∈ blockChoices n, (wtβ L : ℝ) * G L =
      ∑ L ∈ blockChoices n, (wtβ L : ℝ) * ((1 / 2 ^ I) * ∑ e : Fin I → Bool, G (kmSwap I e L)) := by
  have h1 : ∀ e : Fin I → Bool, ∑ L ∈ blockChoices n, (wtβ L : ℝ) * G L =
      ∑ L ∈ blockChoices n, (wtβ L : ℝ) * G (kmSwap I e L) := by
    intro e
    refine Finset.sum_nbij' (kmSwap I e) (kmSwap I e) ?_ ?_ ?_ ?_ ?_
    · intro L hL; rw [fam_mem_blockChoices] at hL ⊢; rw [km_swap_length]; exact hL
    · intro L hL; rw [fam_mem_blockChoices] at hL ⊢; rw [km_swap_length]; exact hL
    · intro L _; exact km_swap_invol I e L
    · intro L _; exact km_swap_invol I e L
    · intro L _; rw [km_swap_wt, km_swap_invol]
  have hcard : ((Finset.univ : Finset (Fin I → Bool)).card : ℝ) = 2 ^ I := by
    rw [Finset.card_univ]; simp
  have h2 : ∑ L ∈ blockChoices n, (wtβ L : ℝ) * G L =
      (1 / 2 ^ I) * ∑ e : Fin I → Bool, ∑ L ∈ blockChoices n, (wtβ L : ℝ) * G (kmSwap I e L) := by
    rw [← Finset.sum_congr rfl (fun e _ => h1 e), Finset.sum_const, nsmul_eq_mul, hcard]
    field_simp
  rw [h2, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun L _ => ?_)
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  ring

/-! ### The law `keyLaw` of the sum over coins -/

lemma km_law_nonneg (V I : ℕ) (z : ZMod (2 ^ V)) (a : Fin I → ZMod (2 ^ V)) (x : ZMod (2 ^ V)) :
    0 ≤ keyLaw V I z a x := by
  unfold keyLaw; positivity

lemma km_law_le_one (V I : ℕ) (z : ZMod (2 ^ V)) (a : Fin I → ZMod (2 ^ V)) (x : ZMod (2 ^ V)) :
    keyLaw V I z a x ≤ 1 := by
  unfold keyLaw
  rw [div_le_one (by positivity)]
  have h := Finset.card_filter_le (Finset.univ : Finset (Fin I → Bool))
    (fun e => z + ∑ j, (if e j then a j else 0) = x)
  rw [Finset.card_univ] at h
  have h2 : (Fintype.card (Fin I → Bool) : ℝ) = 2 ^ I := by simp
  calc (((Finset.univ.filter (fun e : Fin I → Bool => z + ∑ j, (if e j then a j else 0) = x)).card : ℕ) : ℝ)
      ≤ (Fintype.card (Fin I → Bool) : ℝ) := by exact_mod_cast h
    _ = 2 ^ I := h2

lemma km_law_sum (V I : ℕ) (z : ZMod (2 ^ V)) (a : Fin I → ZMod (2 ^ V)) :
    ∑ x, keyLaw V I z a x = 1 := by
  unfold keyLaw
  rw [← Finset.sum_div]
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin I → Bool)))
    (t := (Finset.univ : Finset (ZMod (2 ^ V)))) (f := fun e => z + ∑ j, (if e j then a j else 0))
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  rw [Finset.card_univ] at h
  have h2 : (Fintype.card (Fin I → Bool) : ℝ) = 2 ^ I := by simp
  rw [div_eq_one_iff_eq (by positivity), ← h2]
  rw [h]; push_cast
  rfl

/-- Translation: `keyLaw V I z a x = keyLaw V I 0 a (x - z)`. -/
lemma km_law_shift (V I : ℕ) (z : ZMod (2 ^ V)) (a : Fin I → ZMod (2 ^ V)) (x : ZMod (2 ^ V)) :
    keyLaw V I z a x = keyLaw V I 0 a (x - z) := by
  unfold keyLaw
  have hc : ∀ e : Fin I → Bool, (z + ∑ j, (if e j then a j else 0) = x) ↔
      (0 + ∑ j, (if e j then a j else 0) = x - z) := by
    intro e; constructor <;> intro h <;> linear_combination h
  rw [Finset.filter_congr (fun e _ => hc e)]

/-- Part of **(Q1)**: `Q_λ` does not change under translations. -/
lemma km_Q_shift (V lam I : ℕ) (z : ZMod (2 ^ V)) (a : Fin I → ZMod (2 ^ V)) :
    keyQ V lam (keyLaw V I z a) = keyQ V lam (keyLaw V I 0 a) := by
  unfold keyQ
  have hF : ∀ x, keyF V lam (keyLaw V I z a) x = keyF V lam (keyLaw V I 0 a) (x - z) := by
    intro x
    unfold keyF
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [km_law_shift]; congr 1; ring
  simp_rw [hF]
  exact Equiv.sum_comp (Equiv.subRight z) (fun x => (keyF V lam (keyLaw V I 0 a) x - (lam : ℝ) / 2 ^ V) ^ 2)

lemma km_Q_nonneg (V lam : ℕ) (μ : ZMod (2 ^ V) → ℝ) : 0 ≤ keyQ V lam μ := by
  unfold keyQ; positivity

/-- Crude bound: if `0 ≤ μ ≤ 1`, then `Q_λ(μ) ≤ 2^V λ^2`. -/
lemma km_Q_le (V lam : ℕ) (μ : ZMod (2 ^ V) → ℝ) (h0 : ∀ x, 0 ≤ μ x) (h1 : ∀ x, μ x ≤ 1) :
    keyQ V lam μ ≤ 2 ^ V * (lam : ℝ) ^ 2 := by
  unfold keyQ
  have hF : ∀ x, 0 ≤ keyF V lam μ x ∧ keyF V lam μ x ≤ lam := by
    intro x
    unfold keyF
    refine ⟨Finset.sum_nonneg (fun y _ => h0 _), ?_⟩
    calc ∑ y ∈ Finset.range lam, μ (x + (y : ZMod (2 ^ V))) ≤ ∑ _y ∈ Finset.range lam, (1 : ℝ) :=
          Finset.sum_le_sum (fun y _ => h1 _)
      _ = lam := by simp
  have hc : 0 ≤ (lam : ℝ) / 2 ^ V ∧ (lam : ℝ) / 2 ^ V ≤ lam := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ 2 ^ V := one_le_pow₀ (by norm_num)
    nlinarith [Nat.cast_nonneg (α := ℝ) lam]
  calc ∑ x : ZMod (2 ^ V), (keyF V lam μ x - (lam : ℝ) / 2 ^ V) ^ 2
      ≤ ∑ _x : ZMod (2 ^ V), (lam : ℝ) ^ 2 := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        obtain ⟨a1, a2⟩ := hF x
        obtain ⟨c1, c2⟩ := hc
        nlinarith
    _ = 2 ^ V * (lam : ℝ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; push_cast; ring

/-! ### Cells -/

/-- For a natural number `ρ`, `Σ_{y<h} [ρ = u h + y] = [ρ / h = u]`. -/
lemma km_sum_cell (ρ u h : ℕ) (hh : 0 < h) :
    ∑ y ∈ Finset.range h, (if ρ = u * h + y then (1 : ℝ) else 0) = if ρ / h = u then 1 else 0 := by
  rw [Finset.sum_eq_single (ρ % h)]
  · have hdm := Nat.div_add_mod ρ h
    split_ifs with h1 h2 h2
    · rfl
    · exfalso; apply h2
      have : ρ / h = (u * h + ρ % h) / h := by rw [← h1]
      rw [this, Nat.add_comm, Nat.add_mul_div_right _ _ hh, Nat.div_eq_of_lt (Nat.mod_lt _ hh),
        zero_add]
    · exfalso; apply h1; rw [← h2]; linarith [hdm]
    · rfl
  · intro y hy hne
    split_ifs with h1
    · exfalso; apply hne
      rw [h1, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Finset.mem_range.mp hy)]
    · rfl
  · intro h1; exact absurd (Finset.mem_range.mpr (Nat.mod_lt _ hh)) h1

/-- **The cell formula**: if `ρ(e) < 2^V` and `(ρ(e) : ZMod 2^V) = z₀ + Σ_j e_j a_j`, then the measure under `keyLaw` of the cell `C_u` is
the proportion of `e` for which the top `ℓ` digits of `ρ(e)` are `u`. -/
theorem km_cell (V ℓ I : ℕ) (hℓ : ℓ ≤ V) (z : ZMod (2 ^ V)) (a : Fin I → ZMod (2 ^ V))
    (ρ : (Fin I → Bool) → ℕ) (hρ : ∀ e, ρ e < 2 ^ V)
    (hsh : ∀ e, (ρ e : ZMod (2 ^ V)) = z + ∑ j, (if e j then a j else 0)) (u : ℕ) (hu : u < 2 ^ ℓ) :
    keyCell V ℓ (keyLaw V I z a) u =
      (1 / 2 ^ I) * ∑ e : Fin I → Bool, (if ρ e / 2 ^ (V - ℓ) = u then (1 : ℝ) else 0) := by
  have hV : 2 ^ V = 2 ^ ℓ * 2 ^ (V - ℓ) := by rw [← pow_add, Nat.add_sub_cancel' hℓ]
  have hh : 0 < 2 ^ (V - ℓ) := by positivity
  unfold keyCell keyLaw
  have hfil : ∀ y ∈ Finset.range (2 ^ (V - ℓ)),
      Finset.univ.filter (fun e : Fin I → Bool => z + ∑ j, (if e j then a j else 0) =
        ((u * 2 ^ (V - ℓ) + y : ℕ) : ZMod (2 ^ V))) =
      Finset.univ.filter (fun e : Fin I → Bool => ρ e = u * 2 ^ (V - ℓ) + y) := by
    intro y hy
    have hlt : u * 2 ^ (V - ℓ) + y < 2 ^ V := by
      have hy' := Finset.mem_range.mp hy
      have : (u + 1) * 2 ^ (V - ℓ) ≤ 2 ^ ℓ * 2 ^ (V - ℓ) := Nat.mul_le_mul_right _ hu
      rw [hV]; nlinarith
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hsh e, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hρ e), Nat.mod_eq_of_lt hlt]
  rw [Finset.sum_congr rfl (fun y hy => by rw [hfil y hy])]
  simp_rw [Finset.card_filter]
  push_cast
  rw [← Finset.sum_div, Finset.sum_comm, div_eq_mul_one_div, mul_comm]
  congr 1
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [← km_sum_cell (ρ e) u (2 ^ (V - ℓ)) hh]

end Collatz.Arctic
