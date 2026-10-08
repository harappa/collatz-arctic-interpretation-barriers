/-
Joined words and the ideal lineage values (a step of the proof of `MinRate` in the general case: Theorem B.3, Step 6, (J1)).

The word obtained by joining the segments `x₀, x₁, …, x_n` of length `L` with the junction words `jw g_k` of realized permutations `g_k` is
`sWord x₀ ps = x₀ jw(g₁) x₁ ⋯ jw(g_n) x_n` (`ps = [(g_n, x_n), …, (g₁, x₁)]`, newest first).

* Each segment is decomposed as `x = p u c u q` (`segDec`); this gives the core `sK` (`c₀ u z₁ u c₁ ⋯`, `z_k = q_{k-1} jw(g_k) p_k`) and the outer parts `sP`, `sQ`.
  If all segments are good, then `sWord = sP u sK u sQ` (`hsp_sWord_eq`).
* **Ideal lineage values** `sV`: `sV (… :: ps) i = sV ps i + a_x (σ i)` with `σ = π_p ∘ g ∘ π_q ∘ π_core` (`a_x = linVal · c_x`).
  The difference from the true lineage values `linVal i (sK …)` is at most `J = M (2h + jwMax + 3|u|)` per junction (`hsp_sV_err`, cocycle).
-/
import CollatzProof.Arctic.HSPSeg

namespace Collatz.Arctic

open MinIdeal Matrix Arc

variable {D : ℕ} {A : Interp D} {C : Finset (Fin D)} (S : LinSetup A C) (h : ℕ)

/-- The list of junction pairs (newest first). -/
abbrev PList (S : LinSetup A C) := List (Equiv.Perm (Cls S.E S.hE) × Word)

/-- The joined word. -/
noncomputable def sWord (x₀ : Word) : PList S → Word
  | [] => x₀
  | (g, x) :: ps => sWord x₀ ps ++ jw S g ++ x

/-- The outer back part (the `q` of the last segment). -/
noncomputable def sQ (x₀ : Word) : PList S → Word
  | [] => (segDec S h x₀).2.2
  | (_, x) :: _ => (segDec S h x).2.2

lemma hsp_sQ_nil (x₀ : Word) : sQ S h x₀ [] = (segDec S h x₀).2.2 := rfl

lemma hsp_sQ_cons (x₀ : Word) (g : Equiv.Perm (Cls S.E S.hE)) (x : Word) (ps : PList S) :
    sQ S h x₀ ((g, x) :: ps) = (segDec S h x).2.2 := rfl

/-- The core. -/
noncomputable def sK (x₀ : Word) : PList S → Word
  | [] => (segDec S h x₀).2.1
  | (g, x) :: ps => sK x₀ ps ++ S.u ++ (sQ S h x₀ ps ++ jw S g ++ (segDec S h x).1) ++ S.u ++
      (segDec S h x).2.1

/-- The permutation of the type of a word (as an `Equiv.Perm`). -/
noncomputable def wPerm (w : Word) : Equiv.Perm (Cls S.E S.hE) :=
  (piX S.hE (suppRel (ev (restrictI C A) w))).toEquiv

/-- The vector of lineage values. -/
noncomputable def prof (c : Word) : Cls S.E S.hE → ℝ := fun i => (linVal S i c : ℝ)

/-- The ideal lineage values. -/
noncomputable def sV (x₀ : Word) : PList S → Cls S.E S.hE → ℝ
  | [] => prof S (segDec S h x₀).2.1
  | (g, x) :: ps => fun i => sV x₀ ps i + prof S (segDec S h x).2.1
      (wPerm S (segDec S h x).1 (g (((wPerm S (sK S h x₀ ps)).trans (wPerm S (sQ S h x₀ ps))) i)))

/-- All segments are good. -/
def AllGood (x₀ : Word) (ps : PList S) : Prop := GoodSeg S h x₀ ∧ ∀ gx ∈ ps, GoodSeg S h gx.2

/-- All segments are digit words and all permutations are realized. -/
def AllOk (x₀ : Word) (ps : PList S) : Prop :=
  IsDigits x₀ ∧ ∀ gx ∈ ps, IsDigits gx.2 ∧ realized S gx.1

lemma hsp_allOk_tail {x₀ : Word} {gx : Equiv.Perm (Cls S.E S.hE) × Word} {ps : PList S}
    (h : AllOk S x₀ (gx :: ps)) : AllOk S x₀ ps :=
  ⟨h.1, fun g hg => h.2 g (List.mem_cons_of_mem _ hg)⟩

lemma hsp_sQ_digits {x₀ : Word} {ps : PList S} (hok : AllOk S x₀ ps) : IsDigits (sQ S h x₀ ps) := by
  cases ps with
  | nil => exact (hsp_segDec_digits S h hok.1).2.2
  | cons gx ps => exact (hsp_segDec_digits S h (hok.2 gx List.mem_cons_self).1).2.2

lemma hsp_sQ_len (x₀ : Word) (ps : PList S) : (sQ S h x₀ ps).length ≤ h := by
  cases ps with
  | nil => exact (hsp_segDec_len S h x₀).2.1
  | cons gx ps => exact (hsp_segDec_len S h gx.2).2.1

lemma hsp_sK_digits {x₀ : Word} : ∀ {ps : PList S}, AllOk S x₀ ps → IsDigits (sK S h x₀ ps)
  | [], hok => (hsp_segDec_digits S h hok.1).2.1
  | (g, x) :: ps, hok => by
    have hx := (hok.2 (g, x) List.mem_cons_self).1
    have h1 := hsp_sK_digits (hsp_allOk_tail S hok)
    have h2 := hsp_sQ_digits S h (hsp_allOk_tail S hok)
    have h3 := hsp_segDec_digits S h hx
    simp only [sK]
    exact hsp_isDigits_append (hsp_isDigits_append (hsp_isDigits_append (hsp_isDigits_append h1 S.hu)
      (hsp_isDigits_append (hsp_isDigits_append h2 (hsp_jw_digits S g)) h3.1)) S.hu) h3.2.1

/-- If all segments are good, then `sWord = sP u sK u sQ`. -/
theorem hsp_sWord_eq {x₀ : Word} : ∀ {ps : PList S}, AllGood S h x₀ ps →
    sWord S x₀ ps = (segDec S h x₀).1 ++ S.u ++ sK S h x₀ ps ++ S.u ++ sQ S h x₀ ps
  | [], hg => by simp only [sWord, sK, hsp_sQ_nil]; exact (hsp_segDec_good S hg.1).1
  | (g, x) :: ps, hg => by
    have hg' : AllGood S h x₀ ps := ⟨hg.1, fun gx hgx => hg.2 gx (List.mem_cons_of_mem _ hgx)⟩
    have ih := hsp_sWord_eq hg'
    have hx : x = (segDec S h x).1 ++ S.u ++ (segDec S h x).2.1 ++ S.u ++ (segDec S h x).2.2 :=
      (hsp_segDec_good S (hg.2 (g, x) List.mem_cons_self)).1
    simp only [sWord, sK, hsp_sQ_cons]
    rw [ih]
    conv_lhs => rw [hx]
    simp only [List.append_assoc]

/-- The error per junction `J = M (2h + jwMax + 3|u|)`. -/
noncomputable def junErr : ℕ := digMax A * (2 * h + jwMax S + 3 * S.u.length)

lemma hsp_sK_cons (x₀ : Word) (g : Equiv.Perm (Cls S.E S.hE)) (x : Word) (ps : PList S) :
    sK S h x₀ ((g, x) :: ps) = sK S h x₀ ps ++ S.u ++
      ((sQ S h x₀ ps ++ jw S g ++ (segDec S h x).1) ++ S.u ++ (segDec S h x).2.1) := by
  simp only [sK, List.append_assoc]

/-- **Difference between the true and the ideal lineage values**: at most `J` per junction. -/
theorem hsp_sV_err {x₀ : Word} : ∀ {ps : PList S}, AllOk S x₀ ps → ∀ i,
    |prof S (sK S h x₀ ps) i - sV S h x₀ ps i| ≤ ps.length * (junErr S h : ℝ)
  | [], _, i => by simp [sK, sV]
  | (g, x) :: ps, hok, i => by
    have hok' := hsp_allOk_tail S hok
    have ih := hsp_sV_err hok' i
    obtain ⟨hx, hg⟩ := hok.2 (g, x) List.mem_cons_self
    have hK := hsp_sK_digits S h hok'
    have hQ := hsp_sQ_digits S h hok'
    obtain ⟨hp, hc, -⟩ := hsp_segDec_digits S h hx
    set K' := sK S h x₀ ps
    set Q' := sQ S h x₀ ps
    set p := (segDec S h x).1
    set c := (segDec S h x).2.1
    set z := Q' ++ jw S g ++ p with hz
    have hzd : IsDigits z := hsp_isDigits_append (hsp_isDigits_append hQ (hsp_jw_digits S g)) hp
    set k := piX S.hE (suppRel (ev (restrictI C A) K')) i with hk
    have hσ : piX S.hE (suppRel (ev (restrictI C A) z)) k =
        wPerm S p (g (((wPerm S K').trans (wPerm S Q')) i)) := by
      rw [hz, hsp_piX_junction S hg hp hQ]
      rfl
    -- cocycle
    have c1 := hsp_lin_cocycle_up S i (z ++ S.u ++ c) hK
    have c2 := hsp_lin_cocycle_low S i hK (hsp_isDigits_append (hsp_isDigits_append hzd S.hu) hc)
    have c3 := hsp_lin_cocycle_up S k c hzd
    have c4 := hsp_lin_cocycle_low S k hzd hc
    rw [hσ] at c3 c4
    rw [← hk] at c1 c2
    have hzb := hsp_lin_bound S k hzd
    have hzl : z.length ≤ 2 * h + jwMax S := by
      have h1 : Q'.length ≤ h := hsp_sQ_len S h x₀ ps
      have h2 : (jw S g).length ≤ jwMax S := hsp_jw_le S ((hsp_mem_realSet S).mpr hg)
      have h3 : p.length ≤ h := (hsp_segDec_len S h x).1
      simp only [hz, List.length_append]
      omega
    have hzb' : linVal S k z ≤ junErr S h := by
      unfold junErr
      refine hzb.trans (Nat.mul_le_mul_left _ ?_)
      omega
    have hU : 2 * (digMax A * S.u.length) ≤ junErr S h := by
      unfold junErr
      calc 2 * (digMax A * S.u.length) = digMax A * (2 * S.u.length) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
    -- conclusion
    have e1 : sK S h x₀ ((g, x) :: ps) = K' ++ S.u ++ (z ++ S.u ++ c) := hsp_sK_cons S h x₀ g x ps
    simp only [prof, sV, List.length_cons]
    rw [e1]
    simp only [prof] at ih
    set a := linVal S (wPerm S p (g (((wPerm S K').trans (wPerm S Q')) i))) c
    have hup : linVal S i (K' ++ S.u ++ (z ++ S.u ++ c)) ≤ linVal S i K' + junErr S h + a := by
      omega
    have hlow : linVal S i K' + a ≤ linVal S i (K' ++ S.u ++ (z ++ S.u ++ c)) + junErr S h := by
      omega
    have hupR : (linVal S i (K' ++ S.u ++ (z ++ S.u ++ c)) : ℝ) ≤
        (linVal S i K' : ℝ) + (junErr S h : ℝ) + (a : ℝ) := by exact_mod_cast hup
    have hlowR : (linVal S i K' : ℝ) + (a : ℝ) ≤
        (linVal S i (K' ++ S.u ++ (z ++ S.u ++ c)) : ℝ) + (junErr S h : ℝ) := by exact_mod_cast hlow
    rw [abs_le] at ih ⊢
    push_cast
    constructor <;> nlinarith [ih.1, ih.2]

end Collatz.Arctic
