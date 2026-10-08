/-
# The lexicographically minimal configuration (Step 0 of the proof of Proposition 12.31 of the paper)

The configuration `conf_lo` minimizing (degree, coefficient) lexicographically and `c_* := min C_{d(conf)}(conf)` of the proof of Proposition 12.31
are chosen under the hypothesis of case B (every configuration of `𝔎` has a positive coefficient of positive degree). When all components are 0/1 the rates are 0 or −∞, so they are not
compared (a configuration is the pair (top window, forward state and residue); the top window is fixed to `(u♯)^R`). The written proof is Section 12.9 of the paper.

* `degF c`: the largest degree with a positive coefficient (at most `D_max`). `degF_spec`.
* `exists_lo`: `d* := min degF ≥ 1`, `conf_lo` (with minimal `C_{d*}` among those with `degF = d*`), `C* > 0`, `c_* > 0`, and
  for every configuration `c` of `𝔎`, "`degF c > d*`" or "`degF c = d*` and `C_{d*}(c) ≥ C*`".
* `prσ_not`: the probability of the complementary event.
-/
import CollatzProof.Arctic.Nat.W3hX1

namespace Collatz.Arctic.NatQ5.W3h

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W3c
open Collatz.Arctic.MinIdeal (BRel)

set_option linter.unusedSectionVars false

namespace Setup

variable {Q : Type} [Fintype Q] [DecidableEq Q] {B : ValAuto Q} (S : Setup B)

theorem coef_eq_zero_of_gt {d : ℕ} (hd : S.Dm < d) (s : BRel (ZIdx B)) : S.coef d s = 0 := by
  unfold coef
  have : Finset.univ.filter (fun γ => S.D.deg γ = d) = ∅ := by
    ext γ; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    have := S.deg_le_Dm γ; omega
  rw [this, Finset.sum_empty, zero_div]

open Classical in
/-- The largest degree with a positive coefficient. -/
noncomputable def degF (s : BRel (ZIdx B)) : ℕ :=
  ((Finset.range (S.Dm + 1)).filter (fun d => 0 < S.coef d s)).sup id

open Classical in
/-- Properties of `degF`: if some positive degree has a positive coefficient, then `degF ≥ 1`, `C_{degF} > 0`, and the coefficients of higher degrees are 0. -/
theorem degF_spec {s : BRel (ZIdx B)} (h : ∃ d, 1 ≤ d ∧ 0 < S.coef d s) :
    1 ≤ S.degF s ∧ 0 < S.coef (S.degF s) s ∧ ∀ d, S.degF s < d → S.coef d s = 0 := by
  obtain ⟨d, hd1, hd⟩ := h
  have hdD : d ≤ S.Dm := by
    by_contra hc; push Not at hc
    rw [S.coef_eq_zero_of_gt hc] at hd; exact lt_irrefl _ hd
  have hmem : d ∈ (Finset.range (S.Dm + 1)).filter (fun d => 0 < S.coef d s) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hd⟩
  have hne : ((Finset.range (S.Dm + 1)).filter (fun d => 0 < S.coef d s)).Nonempty := ⟨d, hmem⟩
  obtain ⟨d', hd', hsup⟩ := Finset.exists_mem_eq_sup _ hne id
  have hle : d ≤ S.degF s := Finset.le_sup (f := id) hmem
  refine ⟨le_trans hd1 hle, ?_, fun d'' hd'' => ?_⟩
  · unfold degF; rw [hsup]; exact (Finset.mem_filter.mp hd').2
  · by_cases hD : d'' ≤ S.Dm
    · have hnot : d'' ∉ (Finset.range (S.Dm + 1)).filter (fun d => 0 < S.coef d s) := by
        intro hm
        have := Finset.le_sup (f := id) hm
        unfold degF at hd''; simp only [id] at this; omega
      rw [Finset.mem_filter] at hnot
      push Not at hnot
      exact le_antisymm (hnot (Finset.mem_range.mpr (by omega))) (S.coef_nonneg d'' s)
    · exact S.coef_eq_zero_of_gt (by omega) s

/-- **The lexicographically minimal configuration** (`conf_lo` and `c_*` of Step 0 of the proof of Proposition 12.31 of the paper). -/
theorem exists_lo (hB : ∀ c ∈ S.Kset, ∃ d, 1 ≤ d ∧ 0 < S.coef d c.1) :
    ∃ clo ∈ S.Kset, ∃ dlo : ℕ, ∃ Clo cs : ℝ,
      1 ≤ dlo ∧ S.degF clo.1 = dlo ∧ Clo = S.coef dlo clo.1 ∧ 0 < Clo ∧ 0 < cs ∧
      (∀ d, dlo < d → S.coef d clo.1 = 0) ∧
      (∀ c ∈ S.Kset, cs ≤ S.coef (S.degF c.1) c.1 ∧
        (dlo < S.degF c.1 ∨ (S.degF c.1 = dlo ∧ Clo ≤ S.coef dlo c.1))) := by
  have hne := S.Kset_nonempty
  obtain ⟨c₀, hc₀, hmin⟩ := Finset.exists_min_image S.Kset (fun c => S.degF c.1) hne
  set dlo := S.degF c₀.1
  classical
  set Kd := S.Kset.filter (fun c => S.degF c.1 = dlo)
  have hKd : Kd.Nonempty := ⟨c₀, Finset.mem_filter.mpr ⟨hc₀, rfl⟩⟩
  obtain ⟨clo, hclo, hmin2⟩ := Finset.exists_min_image Kd (fun c => S.coef dlo c.1) hKd
  rw [Finset.mem_filter] at hclo
  obtain ⟨cs₀, hcs₀, hmin3⟩ := Finset.exists_min_image S.Kset (fun c => S.coef (S.degF c.1) c.1) hne
  have hspec := fun c (hc : c ∈ S.Kset) => S.degF_spec (hB c hc)
  refine ⟨clo, hclo.1, dlo, S.coef dlo clo.1, S.coef (S.degF cs₀.1) cs₀.1,
    (hspec c₀ hc₀).1, hclo.2, rfl, ?_, (hspec cs₀ hcs₀).2.1, ?_, fun c hc => ⟨hmin3 c hc, ?_⟩⟩
  · rw [← hclo.2]; exact (hspec clo hclo.1).2.1
  · intro d hd; rw [← hclo.2] at hd; exact (hspec clo hclo.1).2.2 d hd
  · rcases (hmin c hc).lt_or_eq with h | h
    · left; exact h
    · right
      refine ⟨h.symm, hmin2 c (Finset.mem_filter.mpr ⟨hc, h.symm⟩)⟩

end Setup

/-- The probability of the complementary event: `Prσ(¬E) = 1 - Prσ(E)`. -/
theorem prσ_not (β₀ : List Bool) (k : ℕ) (E : List Bool → Prop) :
    Prσ β₀ k (fun β => ¬ E β) = 1 - Prσ β₀ k E := by
  classical
  have h := Finset.sum_filter_add_sum_filter_not (blockChoices k) (fun β => E (β₀ ++ β)) wtβ
  rw [W3b.sum_wt] at h
  unfold Prσ
  convert (eq_sub_of_add_eq' h) using 2
  ext β; simp only [Finset.mem_filter]

end Collatz.Arctic.NatQ5.W3h
