/-
Lineage values (a step of the proof of `MinRate` in the general case: Theorem B.3, Step 4, (L1)–(L5)). The "lineages"
and the "shape at the end of an occurrence of `u`" (inside a class the Boolean block is all ones; the classes are permuted by the group).

* `linVal S i x`: the largest entry of the product restricted to `C` along the word `x u`, from the indices of the row `β_i` of class `i` (`u` is the word of type `E`).
* The end index of a finite entry lies in `β_{π_x(i)}` (`hsp_lin_supp`). The maximum is attained (`hsp_lin_attained`).
* **Lower estimate** `hsp_lin_low`: every index `t` of `β_{π_x(i)}` is reached with value at least `linVal - M|u|` from the starting index attaining the maximum
  (the row of `E` at the end index `d` of the `x`-part of a maximal path is all of `β_{π_x(i)}`, by the antichain property).
* **Cocycle** `hsp_lin_cocycle_up`, `hsp_lin_cocycle_low`:
  `linVal i x + linVal (π_x i) y - M|u| ≤ linVal i (x u y) ≤ linVal i x + linVal (π_x i) y`.
* **Sandwich** `hsp_lin_entry_low`, `hsp_lin_entry_up`: for a finite entry `v` of the word `u x u` there is a class `j` with
  `linVal j x - M|u| ≤ v`, and a class `j'` with `v ≤ linVal j' x + M|u|`.
-/
import CollatzProof.Arctic.HSPLin

namespace Collatz.Arctic

open MinIdeal Matrix Arc

variable {D : ℕ} {A : Interp D} {C : Finset (Fin D)} (S : LinSetup A C)

/-- The value of lineage `i`: the largest entry of the product restricted to `C` along the word `x u` from the indices of `β_i` (`-∞` read as 0). -/
noncomputable def linVal (i : Cls S.E S.hE) (x : Word) : ℕ := by
  classical exact natOr0 (∑ c ∈ Finset.univ.filter (fun c => beta S.hE i c),
    ∑ t, ev (restrictI C A) (x ++ S.u) c t)

/-- The type of the word `x u` is `X E`. -/
lemma hsp_supp_xu (x : Word) {c t : Fin D} :
    ev (restrictI C A) (x ++ S.u) c t ≠ 0 ↔ (suppRel (ev (restrictI C A) x) * S.E) c t := by
  rw [← S.huE, ← suppRel_ev_append]
  rfl

/-- A finite entry is at most the lineage value. -/
lemma hsp_lin_le {i : Cls S.E S.hE} {x : Word} {c t : Fin D} (hc : beta S.hE i c) {v : ℕ}
    (h : ev (restrictI C A) (x ++ S.u) c t = fin v) : v ≤ linVal S i x := by
  classical
  unfold linVal
  have h1 : ev (restrictI C A) (x ++ S.u) c t ≤ ∑ c ∈ Finset.univ.filter (fun c => beta S.hE i c),
      ∑ t, ev (restrictI C A) (x ++ S.u) c t :=
    (le_sum_of_mem (s := Finset.univ) (fun t => ev (restrictI C A) (x ++ S.u) c t)
      (Finset.mem_univ t)).trans
      (le_sum_of_mem (s := Finset.univ.filter (fun c => beta S.hE i c))
        (fun c => ∑ t, ev (restrictI C A) (x ++ S.u) c t) (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩))
  have := natOr0_mono h1
  rw [h, natOr0_fin] at this
  convert this

/-- The end index of a finite entry lies in `β_{π_x(i)}`. -/
lemma hsp_lin_supp {i : Cls S.E S.hE} {x : Word} (hx : IsDigits x) {c t : Fin D}
    (hc : beta S.hE i c) (h : ev (restrictI C A) (x ++ S.u) c t ≠ 0) :
    beta S.hE (piX S.hE (suppRel (ev (restrictI C A) x)) i) t :=
  carry_one S.hE (S.hgrp _ (hsp_typ_mem hx)) hc ((hsp_supp_xu S x).mp h)

/-- The lineage value is attained. -/
lemma hsp_lin_attained (i : Cls S.E S.hE) {x : Word} (hx : IsDigits x) :
    ∃ c, beta S.hE i c ∧ ∃ t, ev (restrictI C A) (x ++ S.u) c t = fin (linVal S i x) := by
  classical
  set X := suppRel (ev (restrictI C A) x)
  obtain ⟨b, hb⟩ := beta_nonempty S.hE (piX S.hE X i)
  obtain ⟨k, hk, hkb⟩ := (act_beta S.hE (S.hgrp _ (hsp_typ_mem hx)) i b).2 hb
  have hne : (Finset.univ.filter (fun c => beta S.hE i c)).Nonempty :=
    ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
  obtain ⟨c, hc, hcs⟩ := exists_eq_sum hne (fun c => ∑ t, ev (restrictI C A) (x ++ S.u) c t)
  have hune : (Finset.univ : Finset (Fin D)).Nonempty := ⟨k, Finset.mem_univ _⟩
  obtain ⟨t, -, hts⟩ := exists_eq_sum hune (fun t => ev (restrictI C A) (x ++ S.u) c t)
  refine ⟨c, (Finset.mem_filter.mp hc).2, t, ?_⟩
  -- the sum is finite
  have hpos : ev (restrictI C A) (x ++ S.u) k b ≠ 0 := (hsp_supp_xu S x).mpr hkb
  obtain ⟨v₀, hv₀⟩ := hsp_ne_zero_iff_fin.mp hpos
  have hle : fin v₀ ≤ ev (restrictI C A) (x ++ S.u) c t := by
    rw [hts, hcs, ← hv₀]
    exact (le_sum_of_mem (s := Finset.univ) (fun t => ev (restrictI C A) (x ++ S.u) k t)
      (Finset.mem_univ b)).trans
      (le_sum_of_mem (s := Finset.univ.filter (fun c => beta S.hE i c))
        (fun c => ∑ t, ev (restrictI C A) (x ++ S.u) c t) (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩))
  have hne' : ev (restrictI C A) (x ++ S.u) c t ≠ 0 := by
    intro h0
    rw [h0] at hle
    have := (le_iff_val _ _).mp hle
    simp at this
  obtain ⟨v, hv⟩ := hsp_ne_zero_iff_fin.mp hne'
  rw [hv]
  congr 1
  unfold linVal
  rw [← hcs, ← hts, hv, natOr0_fin]

/-- A finite entry of the word `u` of type `E` is at most `digMax · |u|`. -/
lemma hsp_u_le {d t : Fin D} {b : ℕ} (h : ev (restrictI C A) S.u d t = fin b) :
    b ≤ digMax A * S.u.length :=
  (hsp_le_fmax_of h).trans (hsp_fmax_le_digits A C S.u S.hu)

lemma hsp_u_ne_iff {d t : Fin D} : ev (restrictI C A) S.u d t ≠ 0 ↔ S.E d t := by
  rw [← S.huE]; rfl

/-- **Lower estimate**: every index `t` of `β_{π_x(i)}` is reached from some `c ∈ β_i` with value at least `linVal - M|u|`. -/
theorem hsp_lin_low (i : Cls S.E S.hE) {x : Word} (hx : IsDigits x) {t : Fin D}
    (ht : beta S.hE (piX S.hE (suppRel (ev (restrictI C A) x)) i) t) :
    ∃ c, beta S.hE i c ∧ ∃ v, ev (restrictI C A) (x ++ S.u) c t = fin v ∧
      linVal S i x ≤ v + digMax A * S.u.length := by
  set X := suppRel (ev (restrictI C A) x) with hXdef
  have hXg := S.hgrp _ (hsp_typ_mem (A := A) (C := C) hx)
  obtain ⟨c, hc, t', ht'⟩ := hsp_lin_attained S i hx
  rw [ev_append] at ht'
  obtain ⟨d, a, b, hcd, hdt', hab⟩ := hsp_mul_eq_fin ht'
  have hb := hsp_u_le S hdt'
  -- the row of `E` at `d` contains `β_{π_x(i)}`
  have hEdt' : S.E d t' := (hsp_u_ne_iff S).mp (by rw [hdt']; exact hsp_ne_zero_iff_fin.mpr ⟨b, rfl⟩)
  obtain ⟨j, hj, -⟩ := (row_eq_union S.hE d t').mp hEdt'
  have hXcd : X c d := by
    show ev (restrictI C A) x c d ≠ 0
    rw [hcd]; exact hsp_ne_zero_iff_fin.mpr ⟨a, rfl⟩
  have hsub : ∀ b', beta S.hE j b' → beta S.hE (piX S.hE X i) b' := by
    intro b' hb'
    have hEdb : S.E d b' := (row_eq_union S.hE d b').mpr ⟨j, hj, hb'⟩
    exact carry_one S.hE hXg hc ((BRel.mul_apply _ _ _ _).2 ⟨d, hXcd, hEdb⟩)
  have hji : piX S.hE X i = j := S.hanti _ _ ((beta_subset_iff S.hE _ _).mp hsub)
  have hEdt : S.E d t := (row_eq_union S.hE d t).mpr ⟨j, hj, hji ▸ ht⟩
  obtain ⟨b', hb'⟩ := hsp_ne_zero_iff_fin.mp ((hsp_u_ne_iff S).mpr hEdt)
  -- `c → d → t`
  have hle : fin (a + b') ≤ ev (restrictI C A) (x ++ S.u) c t := by
    rw [ev_append, ← fin_mul_fin, ← hcd, ← hb']
    exact hsp_le_mul_apply _ _ c d t
  have hne : ev (restrictI C A) (x ++ S.u) c t ≠ 0 := by
    intro h0; rw [h0] at hle; have := (le_iff_val _ _).mp hle; simp at this
  obtain ⟨v, hv⟩ := hsp_ne_zero_iff_fin.mp hne
  rw [hv, fin_le_fin] at hle
  refine ⟨c, hc, v, hv, ?_⟩
  omega

/-- The lineage value is at most `M (|x| + |u|)`. -/
lemma hsp_lin_bound (i : Cls S.E S.hE) {x : Word} (hx : IsDigits x) :
    linVal S i x ≤ digMax A * (x.length + S.u.length) := by
  obtain ⟨c, -, t, ht⟩ := hsp_lin_attained S i hx
  have := (hsp_le_fmax_of ht).trans
    (hsp_fmax_le_digits A C _ (hsp_isDigits_append hx S.hu))
  rwa [List.length_append] at this

lemma hsp_xuyu (x y : Word) : x ++ S.u ++ y ++ S.u = (x ++ S.u) ++ (y ++ S.u) := by
  simp [List.append_assoc]

/-- **Cocycle (upper)**: `linVal i (x u y) ≤ linVal i x + linVal (π_x i) y`. -/
theorem hsp_lin_cocycle_up (i : Cls S.E S.hE) {x : Word} (y : Word) (hx : IsDigits x) :
    linVal S i (x ++ S.u ++ y) ≤
      linVal S i x + linVal S (piX S.hE (suppRel (ev (restrictI C A) x)) i) y := by
  classical
  unfold linVal
  refine natOr0_sum_le _ _ (fun c hc => natOr0_sum_le _ _ (fun t _ => natOr0_le_of (fun v hv => ?_)))
  have hc' := (Finset.mem_filter.mp hc).2
  rw [hsp_xuyu, ev_append] at hv
  obtain ⟨k, a, b, hck, hkt, hab⟩ := hsp_mul_eq_fin hv
  have hk := hsp_lin_supp S hx hc' (by rw [hck]; exact hsp_ne_zero_iff_fin.mpr ⟨a, rfl⟩)
  have h1 := hsp_lin_le S hc' hck
  have h2 := hsp_lin_le S hk hkt
  unfold linVal at h1 h2
  omega

/-- **Cocycle (lower)**: `linVal i x + linVal (π_x i) y ≤ linVal i (x u y) + M|u|`. -/
theorem hsp_lin_cocycle_low (i : Cls S.E S.hE) {x y : Word} (hx : IsDigits x) (hy : IsDigits y) :
    linVal S i x + linVal S (piX S.hE (suppRel (ev (restrictI C A) x)) i) y ≤
      linVal S i (x ++ S.u ++ y) + digMax A * S.u.length := by
  set j := piX S.hE (suppRel (ev (restrictI C A) x)) i
  obtain ⟨c', hc', t', ht'⟩ := hsp_lin_attained S j hy
  obtain ⟨c, hc, v, hv, hvle⟩ := hsp_lin_low S i hx hc'
  have hle : fin (v + linVal S j y) ≤ ev (restrictI C A) (x ++ S.u ++ y ++ S.u) c t' := by
    rw [hsp_xuyu, ev_append, ← fin_mul_fin, ← hv, ← ht']
    exact hsp_le_mul_apply _ _ c c' t'
  have hne : ev (restrictI C A) (x ++ S.u ++ y ++ S.u) c t' ≠ 0 := by
    intro h0; rw [h0] at hle; have := (le_iff_val _ _).mp hle; simp at this
  obtain ⟨w, hw⟩ := hsp_ne_zero_iff_fin.mp hne
  rw [hw, fin_le_fin] at hle
  have := hsp_lin_le S hc (x := x ++ S.u ++ y) hw
  omega

/-- **Sandwich (lower)**: for a finite entry `v` of the word `u x u` there is a class `j` with `linVal j x ≤ v + M|u|`. -/
theorem hsp_lin_entry_low {x : Word} (hx : IsDigits x) {s t : Fin D} {v : ℕ}
    (h : ev (restrictI C A) (S.u ++ x ++ S.u) s t = fin v) :
    ∃ j, linVal S j x ≤ v + digMax A * S.u.length := by
  rw [List.append_assoc, ev_append] at h
  obtain ⟨c, a, b, hsc, hct, -⟩ := hsp_mul_eq_fin h
  have hEsc : S.E s c := (hsp_u_ne_iff S).mp (by rw [hsc]; exact hsp_ne_zero_iff_fin.mpr ⟨a, rfl⟩)
  obtain ⟨j, hj, hjc⟩ := (row_eq_union S.hE s c).mp hEsc
  have ht := hsp_lin_supp S hx hjc (by rw [hct]; exact hsp_ne_zero_iff_fin.mpr ⟨b, rfl⟩)
  obtain ⟨c', hc', v', hv', hle⟩ := hsp_lin_low S j hx ht
  have hEsc' : S.E s c' := (row_eq_union S.hE s c').mpr ⟨j, hj, hc'⟩
  obtain ⟨a', ha'⟩ := hsp_ne_zero_iff_fin.mp ((hsp_u_ne_iff S).mpr hEsc')
  have hge : fin (a' + v') ≤ fin v := by
    rw [← h, ← fin_mul_fin, ← ha', ← hv']
    exact hsp_le_mul_apply _ _ s c' t
  rw [fin_le_fin] at hge
  exact ⟨j, by omega⟩

/-- **Sandwich (upper)**: for a finite entry `v` of the word `u x u` there is a class `j` with `v ≤ linVal j x + M|u|`. -/
theorem hsp_lin_entry_up {x : Word} {s t : Fin D} {v : ℕ}
    (h : ev (restrictI C A) (S.u ++ x ++ S.u) s t = fin v) :
    ∃ j, v ≤ linVal S j x + digMax A * S.u.length := by
  rw [List.append_assoc, ev_append] at h
  obtain ⟨c, a, b, hsc, hct, hab⟩ := hsp_mul_eq_fin h
  have hEsc : S.E s c := (hsp_u_ne_iff S).mp (by rw [hsc]; exact hsp_ne_zero_iff_fin.mpr ⟨a, rfl⟩)
  obtain ⟨j, -, hjc⟩ := (row_eq_union S.hE s c).mp hEsc
  have h1 := hsp_lin_le S hjc hct
  have h2 := hsp_u_le S hsc
  exact ⟨j, by omega⟩

end Collatz.Arctic
