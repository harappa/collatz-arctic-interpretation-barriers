/-
Variance of values over the classes (a step of the proof of `MinRate` in the general case: Theorem B.3, Step 5, (V1)–(V4)). The mean `pmean` and the
variance `pvar := Σ (v_i - mean)²` of a real-valued function on a finite set `ι` (the classes).

* **Averaging over the permutations removes the cross terms** `hsp_pvar_avg`: if `G` is a finite set of permutations such that the number of `g` with `g k = j` does not depend on `j`
  (a transitive group), then `Σ_{g ∈ G} pvar (a + b ∘ (P g Q)) = |G| (pvar a + pvar b)`. This is a second-order form of the mixing of
  the lineages by the permutations between the classes.
* `hsp_pvar_ge`: `(v_i - v_j)² ≤ 2 pvar v`. `hsp_pvar_perturb`: if all components are within `e`, then `pvar v ≤ 2 pvar w + 2|ι| e²`.
  `hsp_pvar_le`: if `|v_i| ≤ B`, then `pvar v ≤ |ι| B²`.
-/
import Mathlib

namespace Collatz.Arctic

variable {ι : Type*} [Fintype ι]

/-- The mean. -/
noncomputable def pmean (v : ι → ℝ) : ℝ := (∑ i, v i) / Fintype.card ι

/-- The variance (the sum of the squared deviations from the mean). -/
noncomputable def pvar (v : ι → ℝ) : ℝ := ∑ i, (v i - pmean v) ^ 2

lemma hsp_pvar_nonneg (v : ι → ℝ) : 0 ≤ pvar v := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma hsp_sum_sub_pmean (v : ι → ℝ) : ∑ i, (v i - pmean v) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, pmean]
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp h
    simp
  · have : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast h.ne'
    field_simp
    ring

lemma hsp_pmean_perm (v : ι → ℝ) (σ : Equiv.Perm ι) : pmean (fun i => v (σ i)) = pmean v := by
  unfold pmean
  rw [Equiv.sum_comp σ v]

lemma hsp_pvar_perm (v : ι → ℝ) (σ : Equiv.Perm ι) : pvar (fun i => v (σ i)) = pvar v := by
  unfold pvar
  rw [hsp_pmean_perm]
  exact Equiv.sum_comp σ (fun j => (v j - pmean v) ^ 2)

lemma hsp_pmean_add (a b : ι → ℝ) : pmean (fun i => a i + b i) = pmean a + pmean b := by
  unfold pmean
  rw [Finset.sum_add_distrib, add_div]

lemma hsp_pvar_add (a b : ι → ℝ) :
    pvar (fun i => a i + b i) = pvar a + pvar b + 2 * ∑ i, (a i - pmean a) * (b i - pmean b) := by
  unfold pvar
  rw [hsp_pmean_add]
  have e : ∀ i, (a i + b i - (pmean a + pmean b)) ^ 2 =
      (a i - pmean a) ^ 2 + (b i - pmean b) ^ 2 + 2 * ((a i - pmean a) * (b i - pmean b)) := by
    intro i; ring
  simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Rewrite the sum over a set of permutations using the number of permutations sending `k` to each `j`. -/
lemma hsp_sum_perm_fiber [DecidableEq ι] (G : Finset (Equiv.Perm ι))
    (hfib : ∀ k j, (G.filter (fun g => g k = j)).card = (G.filter (fun g => g k = k)).card)
    (φ : ι → ℝ) (k : ι) :
    ∑ g ∈ G, φ (g k) = ((G.filter (fun g => g k = k)).card : ℝ) * ∑ j, φ j := by
  rw [← Finset.sum_fiberwise G (fun g => g k) (fun g => φ (g k)), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_congr rfl (fun g hg => by rw [(Finset.mem_filter.mp hg).2]), Finset.sum_const,
    nsmul_eq_mul, hfib k j]

/-- **Averaging over the permutations removes the cross terms**. -/
theorem hsp_pvar_avg [DecidableEq ι] (G : Finset (Equiv.Perm ι))
    (hfib : ∀ k j, (G.filter (fun g => g k = j)).card = (G.filter (fun g => g k = k)).card)
    (a b : ι → ℝ) (P Q : Equiv.Perm ι) :
    ∑ g ∈ G, pvar (fun i => a i + b (P (g (Q i)))) = G.card * (pvar a + pvar b) := by
  have h1 : ∀ g : Equiv.Perm ι, pvar (fun i => a i + b (P (g (Q i)))) =
      pvar a + pvar b + 2 * ∑ i, (a i - pmean a) * (b (P (g (Q i))) - pmean b) := by
    intro g
    rw [hsp_pvar_add a (fun i => b (P (g (Q i))))]
    have hm : pmean (fun i => b (P (g (Q i)))) = pmean b :=
      hsp_pmean_perm b (Q.trans (g.trans P))
    have hv : pvar (fun i => b (P (g (Q i)))) = pvar b := hsp_pvar_perm b (Q.trans (g.trans P))
    rw [hm, hv]
  simp_rw [h1, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have h2 : ∀ i, ∑ g ∈ G, (a i - pmean a) * (b (P (g (Q i))) - pmean b) = 0 := by
    intro i
    rw [← Finset.mul_sum, hsp_sum_perm_fiber G hfib (fun j => b (P j) - pmean b) (Q i)]
    have h3 : ∑ j, (b (P j) - pmean b) = 0 := by
      rw [Equiv.sum_comp P (fun j => b j - pmean b)]
      exact hsp_sum_sub_pmean b
    rw [h3]; ring
  simp_rw [h2, Finset.sum_const_zero]
  ring

/-- `(v_i - v_j)² ≤ 2 pvar v`. -/
lemma hsp_pvar_ge [DecidableEq ι] (v : ι → ℝ) (i j : ι) : (v i - v j) ^ 2 ≤ 2 * pvar v := by
  by_cases hij : i = j
  · rw [hij, sub_self]; nlinarith [hsp_pvar_nonneg v]
  · have h1 : (v i - pmean v) ^ 2 + (v j - pmean v) ^ 2 ≤ pvar v := by
      unfold pvar
      rw [← Finset.sum_pair hij (f := fun k => (v k - pmean v) ^ 2)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => sq_nonneg _)
    nlinarith [sq_nonneg (v i - pmean v + (v j - pmean v))]

/-- If all components are within `e`, then `pvar v ≤ 2 pvar w + 2 |ι| e²`. -/
lemma hsp_pvar_perturb (v w : ι → ℝ) (e : ℝ) (h : ∀ i, |v i - w i| ≤ e) :
    pvar v ≤ 2 * pvar w + 2 * (Fintype.card ι * e ^ 2) := by
  set d : ι → ℝ := fun i => v i - w i
  have hv : v = fun i => w i + d i := by funext i; simp [d]
  have hmean : pmean v = pmean w + pmean d := by rw [hv, hsp_pmean_add]
  have hpt : ∀ i, (v i - pmean v) ^ 2 ≤ 2 * (w i - pmean w) ^ 2 + 2 * (d i - pmean d) ^ 2 := by
    intro i
    rw [hmean]
    have : v i - (pmean w + pmean d) = (w i - pmean w) + (d i - pmean d) := by simp [d]; ring
    rw [this]
    nlinarith [sq_nonneg ((w i - pmean w) - (d i - pmean d))]
  have hd : ∑ i, (d i - pmean d) ^ 2 ≤ Fintype.card ι * e ^ 2 := by
    have e1 : ∑ i, (d i - pmean d) ^ 2 = ∑ i, d i ^ 2 - Fintype.card ι * pmean d ^ 2 := by
      have hs := hsp_sum_sub_pmean d
      have : ∀ i, (d i - pmean d) ^ 2 = d i ^ 2 - 2 * pmean d * (d i - pmean d) - pmean d ^ 2 := by
        intro i; ring
      simp_rw [this, Finset.sum_sub_distrib, ← Finset.mul_sum, hs, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      ring
    have e2 : ∑ i, d i ^ 2 ≤ ∑ _i : ι, e ^ 2 := Finset.sum_le_sum (fun i _ => by
      have := h i
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at e2
    nlinarith [sq_nonneg (pmean d), (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ _)]
  unfold pvar
  calc ∑ i, (v i - pmean v) ^ 2 ≤ ∑ i, (2 * (w i - pmean w) ^ 2 + 2 * (d i - pmean d) ^ 2) :=
        Finset.sum_le_sum (fun i _ => hpt i)
    _ = 2 * ∑ i, (w i - pmean w) ^ 2 + 2 * ∑ i, (d i - pmean d) ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * ∑ i, (w i - pmean w) ^ 2 + 2 * (Fintype.card ι * e ^ 2) := by linarith

/-- If `0 ≤ v_i ≤ B`, then `pvar v ≤ |ι| B²`. -/
lemma hsp_pvar_le (v : ι → ℝ) (B : ℝ) (h0 : ∀ i, 0 ≤ v i) (h : ∀ i, v i ≤ B) :
    pvar v ≤ Fintype.card ι * B ^ 2 := by
  have e1 : pvar v = ∑ i, v i ^ 2 - Fintype.card ι * pmean v ^ 2 := by
    unfold pvar
    have hs := hsp_sum_sub_pmean v
    have : ∀ i, (v i - pmean v) ^ 2 = v i ^ 2 - 2 * pmean v * (v i - pmean v) - pmean v ^ 2 := by
      intro i; ring
    simp_rw [this, Finset.sum_sub_distrib, ← Finset.mul_sum, hs, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    ring
  have e2 : ∑ i, v i ^ 2 ≤ ∑ _i : ι, B ^ 2 :=
    Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (h0 i) (h i) 2)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at e2
  nlinarith [sq_nonneg (pmean v), (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ _)]

end Collatz.Arctic
