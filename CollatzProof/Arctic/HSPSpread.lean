/-
Spread and the difference of lineage values (a step of the proof of `MinRate` in the general case: Theorem B.3, Step 6, (J4)).

* `hsp_fmin_attained`: if there is a finite entry, `fmin` is the value of some entry.
* **Spread and the difference of lineage values** `hsp_spr_le_lin`: for a joined word `W = P u K u Q` whose segments are all good (`|P|, |Q| ≤ h`),
  there are classes `j₁, j₂` with `spr W ≤ linVal j₁ K - linVal j₂ K + 2Mh + 2M|u|` (no digit word kills `C`; by the sandwich, subadditivity and superadditivity).
-/
import CollatzProof.Arctic.HSPStructSum

namespace Collatz.Arctic

open MinIdeal Matrix Arc Classical

variable {D : ℕ} {A : Interp D} {C : Finset (Fin D)}

/-- If there is a finite entry, `fmin` is the value of some entry. -/
lemma hsp_fmin_attained {w : Word} (hw : IsDigits w) {s₀ t₀ : Fin D}
    (h0 : ev (restrictI C A) w s₀ t₀ ≠ 0) : ∃ s t, ev (restrictI C A) w s t = fin (fmin A C w) := by
  by_contra H
  push Not at H
  obtain ⟨v₀, hv₀⟩ := hsp_ne_zero_iff_fin.mp h0
  set m := fmin A C w
  have hge : ∀ s t v, ev (restrictI C A) w s t = fin v → m + 1 ≤ v := by
    intro s t v hv
    have h1 : m ≤ v := hsp_fmin_le_of hv
    have h2 : v ≠ m := fun e => H s t (e ▸ hv)
    omega
  have hcap : m ≤ digMax A * w.length := hsp_fmin_le A C w
  have hv₀le : v₀ ≤ digMax A * w.length :=
    (hsp_le_fmax_of hv₀).trans (hsp_fmax_le_digits A C w hw)
  have h3 := hge s₀ t₀ v₀ hv₀
  have h4 : m + 1 ≤ m :=
    (hsp_le_minCap (c := digMax A * w.length) (P := ev (restrictI C A) w) (m := m + 1)).mpr
      ⟨by omega, hge⟩
  omega

variable (S : LinSetup A C)

/-- If no digit word kills `C`, there is a class. -/
lemma hsp_cls_nonempty (hND : NeverDies A C C) : Nonempty (Cls S.E S.hE) := by
  obtain ⟨i, -, j, hij⟩ := hND S.u S.hu
  refine nonempty_cls S.hE ⟨i, j, ?_⟩
  rw [← S.huE]; exact hij

/-- The largest entry is the value of some entry (if there is a finite entry). -/
lemma hsp_fmax_attained {w : Word} {s₀ t₀ : Fin D} (h0 : ev (restrictI C A) w s₀ t₀ ≠ 0) :
    ∃ s t, ev (restrictI C A) w s t = fin (fmax A C w) := by
  obtain ⟨i₀, j₀, hij⟩ := hsp_maxEnt_eq (ev (restrictI C A) w) s₀
  have hle : ev (restrictI C A) w s₀ t₀ ≤ maxEnt (ev (restrictI C A) w) :=
    (le_sum_of_mem (s := Finset.univ) (fun j => ev (restrictI C A) w s₀ j) (Finset.mem_univ t₀)).trans
      (le_sum_of_mem (s := Finset.univ) (fun i => ∑ j, ev (restrictI C A) w i j) (Finset.mem_univ s₀))
  have hne : ev (restrictI C A) w i₀ j₀ ≠ 0 := by
    intro h
    have hle' := hle.trans (hij.trans h).le
    have := (le_iff_val _ _).mp hle'
    have h0' := (Arc.ne_zero_iff_val _).mp h0
    exact h0' (le_bot_iff.mp this)
  obtain ⟨v, hv⟩ := hsp_ne_zero_iff_fin.mp hne
  refine ⟨i₀, j₀, ?_⟩
  rw [hv]
  unfold fmax
  rw [hij, hv, natOr0_fin]

/-- **Spread and the difference of lineage values**. -/
theorem hsp_spr_le_lin (hND : NeverDies A C C) {P K Q : Word} (hP : IsDigits P) (hK : IsDigits K)
    (hQ : IsDigits Q) {h : ℕ} (hPl : P.length ≤ h) (hQl : Q.length ≤ h) :
    ∃ j₁ j₂ : Cls S.E S.hE, (spr A C (P ++ S.u ++ K ++ S.u ++ Q) : ℝ) ≤
      (linVal S j₁ K : ℝ) - (linVal S j₂ K : ℝ) + 2 * (digMax A * h : ℕ) +
        2 * (digMax A * S.u.length : ℕ) := by
  set Z := S.u ++ K ++ S.u with hZ
  have hZd : IsDigits Z := hsp_isDigits_append (hsp_isDigits_append S.hu hK) S.hu
  have hW : P ++ S.u ++ K ++ S.u ++ Q = P ++ Z ++ Q := by simp [hZ, List.append_assoc]
  have hWd : IsDigits (P ++ Z ++ Q) := hsp_isDigits_append (hsp_isDigits_append hP hZd) hQ
  rw [hW]
  -- there is a finite entry
  obtain ⟨s₀, -, t₀, h0⟩ := hND Z hZd
  -- maximum
  obtain ⟨s₁, t₁, h1⟩ := hsp_fmax_attained h0
  obtain ⟨j₁, hj₁⟩ := hsp_lin_entry_up S h1
  -- minimum
  obtain ⟨s₂, t₂, h2⟩ := hsp_fmin_attained hZd h0
  obtain ⟨j₂, hj₂⟩ := hsp_lin_entry_low S hK h2
  refine ⟨j₁, j₂, ?_⟩
  -- subadditivity and superadditivity
  have a1 := fmax_append_le A C (P ++ Z) Q
  have a2 := fmax_append_le A C P Z
  have a3 := hsp_fmin_append A C (P ++ Z) Q
  have a4 := hsp_fmin_append A C P Z
  have b1 := (hsp_fmax_le_digits A C P hP).trans (Nat.mul_le_mul_left (digMax A) hPl)
  have b2 := (hsp_fmax_le_digits A C Q hQ).trans (Nat.mul_le_mul_left (digMax A) hQl)
  have hsp := hsp_fmin_le_fmax hND hWd
  have e : (spr A C (P ++ Z ++ Q) : ℝ) = (fmax A C (P ++ Z ++ Q) : ℝ) - (fmin A C (P ++ Z ++ Q) : ℝ) := by
    unfold spr
    rw [Nat.cast_sub hsp]
  rw [e]
  have c1 : fmax A C (P ++ Z ++ Q) ≤
      linVal S j₁ K + digMax A * S.u.length + 2 * (digMax A * h) := by omega
  have c2 : linVal S j₂ K ≤ fmin A C (P ++ Z ++ Q) + digMax A * S.u.length := by omega
  have c1R : (fmax A C (P ++ Z ++ Q) : ℝ) ≤ (linVal S j₁ K : ℝ) + (digMax A * S.u.length : ℕ) +
      2 * (digMax A * h : ℕ) := by exact_mod_cast c1
  have c2R : (linVal S j₂ K : ℝ) ≤ (fmin A C (P ++ Z ++ Q) : ℝ) + (digMax A * S.u.length : ℕ) := by
    exact_mod_cast c2
  push_cast at c1R c2R ⊢
  linarith

end Collatz.Arctic
