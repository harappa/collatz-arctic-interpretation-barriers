/-
Parts of the proof of Lemma 6.5 of the paper (upper bound from window frequencies), (2): transport and components of long stays.
Section 6.3, using Lemma 6.3.

* The rate `rhoB hE A I b` of an index (`Λ_I(b)` in Section 6.3): the supremum of `{Λ_{C(j)} : j ∈ I, j ≤ p ∈ I, b ∈ β_p}` (0 if empty).
* `carry_class` (Lemma 6.3 (ii)–(iv)): if a path spends a whole occurrence `[i, i + |u*|)` of `u*` in one component and
  `i + 2|u*| ≤ T` (`T` is the end of an occurrence of `u*`), then there is a class `j_T` of the upper set `I_T` at time `T` such that the index of the path at time `T`
  lies in `β_{j_T}` and the component is `C(j_T)`.
  - Instead of choosing occurrences greedily from the left and transporting along the sequence `T_1 < T_2 < ⋯`, we use no choice and transport by the single
    permutation `π_X` of the type `X` of the word `Y` from the end `τ` of the occurrence to `T - |u*|` (`(E X E)_c = β_{π_X [c]}`, `C(π_X j) = C(j)`).
    `π_X(j) ∈ I_T` is shown directly from the facts that `c` lies in the support at time `τ` and that the path of `E X E` passes through the support at time `T - |u*|`.
* `stay_long` (components of long stays): if the path stays in one component at the times `[lo, lo + n]` and there is an occurrence of `u*` inside,
  then there is a set `C` of indices of the component with `rate C ≤ Λ_{I_T}(b)` such that the weight on the interval is at most `fmax_C(window)`.
-/
import CollatzProof.Arctic.UpperPath

namespace Collatz.Arctic.Upper

open Collatz.Arctic Collatz.Arctic.MinIdeal Arc

variable {D : ℕ}

/-! ### The rate `Λ_I(b)` of an index -/

section Rho

variable {E : BRel (Fin D)} (hE : E * E = E)

/-- The rate of an index `b`: `Λ_I(b) := max{Λ_{C(j)} : j ∈ I, j ≤ p ∈ I, b ∈ β_p}` (rates and configurations in Section 6.3;
a supremum over a finite set, 0 if empty). -/
noncomputable def rhoB (A : Interp D) (I : Set (Cls E hE)) (b : Fin D) : ℝ :=
  sSup {r | ∃ j ∈ I, (∃ p ∈ I, j ≤ p ∧ beta hE p b) ∧ r = classRate hE A j}

lemma rhoB_nonneg (A : Interp D) (I : Set (Cls E hE)) (b : Fin D) : 0 ≤ rhoB hE A I b :=
  Real.sSup_nonneg (by rintro r ⟨j, -, -, rfl⟩; exact rate_nonneg _ _)

lemma le_rhoB (A : Interp D) {I : Set (Cls E hE)} {b : Fin D} {j : Cls E hE} (hj : j ∈ I)
    (hb : beta hE j b) : classRate hE A j ≤ rhoB hE A I b := by
  have : Finite (Cls E hE) := inferInstanceAs (Finite (Quotient (clsSetoid hE)))
  refine le_csSup ?_ ⟨j, hj, ⟨j, hj, le_rfl, hb⟩, rfl⟩
  refine ((Set.finite_range (classRate hE A)).subset ?_).bddAbove
  rintro r ⟨j', -, -, rfl⟩
  exact ⟨j', rfl⟩

end Rho

/-! ### Transport: the rate of a component of a long stay -/

/-- **Transport** (Lemma 6.3): if a path reads `u*` from time `i` to `i + |u*|` (`i + 2|u*| ≤ T`)
and both ends lie in the same component, then there is a class `j_T` of the upper set `I_T` at time `T` (the end of an occurrence of `u*`) with
`p T ∈ β_{j_T}`, and the index at time `i` lies in the component `C(j_T)`. -/
theorem carry_class (A : Interp D) (u : Fin D → Arc) {K : Set (BRel (Fin D))}
    (hK : IsMinIdeal (Mon (B0 A) (B1 A)) K) {E : BRel (Fin D)} (hEK : E ∈ K) (hE : E * E = E)
    {us : Word} (hEus : suppRel (ev A us) = E)
    {w : Word} (hw : IsDigits w) {T : ℕ} (hT : T ≤ w.length) (hmT : us.length ≤ T)
    (hocc : window w (T - us.length) us.length = us)
    {p : ℕ → Fin D} (hp : IsPath u A w T p) {i : ℕ} (hi : i + us.length + us.length ≤ T)
    (hwin : window w i us.length = us)
    (hreach : Reach (B0 A) (B1 A) (p (i + us.length)) (p i)) :
    ∃ jT : Cls E hE, jT ∈ hitSet hE (suppV (vecAfter u A (w.take (T - us.length)))) ∧
      beta hE jT (p T) ∧ p i ∈ comp (B0 A) (B1 A) hE jT := by
  set m := us.length with hm
  have hEM : E ∈ Mon (B0 A) (B1 A) := hK.1.2.1 hEK
  set S := suppV (vecAfter u A (w.take i)) with hS
  have hpi : p i ∈ S := supp_path hp hT i (by omega)
  have hEi : E (p i) (p (i + m)) := by
    rw [← hEus]
    show ev A us (p i) (p (i + m)) ≠ 0
    rw [← hwin]
    exact path_ev_ne hp hT (by omega)
  obtain ⟨c, hc, -, -, hia, -, hcI, hbeta⟩ := corollary_56_10_2 (B0 A) (B1 A) hK hEK hE
    ⟨reach_path hw hp (by omega) (by omega), hreach⟩ hEi hpi
  set τ := i + m with hτdef
  set Y := window w τ (T - m - τ) with hY
  have hYdig : IsDigits Y := fun s hs => hw s (mem_of_mem_window hs)
  set X := suppRel (ev A Y) with hXdef
  have hXM : X ∈ Mon (B0 A) (B1 A) := suppRel_ev_mem A Y hYdig
  have hX : InH E (E * X * E) := inH_of_minIdeal hK hEK hE hXM
  refine ⟨piX hE X (cls hE c hc), ?_, ?_, ?_⟩
  · obtain ⟨c', hc', hc'eq⟩ := cls_surj hE (piX hE X (cls hE c hc))
    have hb' : beta hE (piX hE X (cls hE c hc)) c' :=
      (beta_mem_C hE _ c' hc').2 (le_of_eq hc'eq.symm)
    rw [← piX_spec hE hX c hc] at hb'
    obtain ⟨z, hz1, hz2⟩ := (BRel.mul_apply _ _ _ _).1 hb'
    obtain ⟨x, hx1, hx2⟩ := (BRel.mul_apply _ _ _ _).1 hz1
    obtain ⟨s, hs, k, hk, hkeq, hsk⟩ := hcI
    have hkc : E k c := ((cls_eq_cls hE hk hc).1 hkeq).1
    have hsx : E s x := trans_of_idem hE (trans_of_idem hE hsk hkc) hx1
    have hτ : suppV (vecAfter u A (w.take τ)) = act S E := by
      rw [hτdef, take_add_window, vecAfter_append, suppV_vecAfter, hwin, hEus]
    have hxτ : x ∈ suppV (vecAfter u A (w.take τ)) := by rw [hτ]; exact ⟨s, hs, hsx⟩
    have hzT : z ∈ suppV (vecAfter u A (w.take (T - m))) := by
      have e : T - m = τ + (T - m - τ) := by omega
      rw [e, take_add_window, vecAfter_append, suppV_vecAfter]
      exact ⟨x, hxτ, hx2⟩
    exact ⟨z, hzT, c', hc', hc'eq, hz2⟩
  · apply carry_one hE hX hbeta
    refine (BRel.mul_apply _ _ _ _).2 ⟨p (T - m), ?_, ?_⟩
    · show ev A Y (p τ) (p (T - m)) ≠ 0
      have := path_ev_ne hp hT (i := τ) (n := T - m - τ) (by omega)
      rwa [show τ + (T - m - τ) = T - m by omega] at this
    · rw [← hEus]
      show ev A us (p (T - m)) (p T) ≠ 0
      rw [← hocc]
      have := path_ev_ne hp hT (i := T - m) (n := m) (by omega)
      rwa [show T - m + m = T by omega] at this
  · rw [comp_piX hE hEM hXM hX]; exact hia

lemma comp_closed {B₀ B₁ E : BRel (Fin D)} {hE : E * E = E} {j : Cls E hE} {a b : Fin D}
    (ha : a ∈ comp B₀ B₁ hE j) (hab : Reach B₀ B₁ a b) (hba : Reach B₀ B₁ b a) :
    b ∈ comp B₀ B₁ hE j := by
  obtain ⟨q', hq', heq, h1, h2⟩ := ha
  exact ⟨q', hq', heq, hba.trans h1, h2.trans hab⟩

open Classical in
lemma exists_classRate_eq {E : BRel (Fin D)} (hE : E * E = E) (A : Interp D) (j : Cls E hE) :
    ∃ C : Finset (Fin D), classRate hE A j = rate A C ∧ ∀ x, x ∈ C ↔ x ∈ comp (B0 A) (B1 A) hE j :=
  ⟨_, rfl, fun _ => Set.mem_toFinset⟩

/-- **Component of a long stay**: if the path stays in one component at the times `[lo, lo + n]` (`q lo` can be reached back from `q (lo + n)`)
and there is an occurrence `[i, i + |u*|)` of `u*` inside (`i + 2|u*| ≤ lo + n`), then there is a set `C` of indices of the component with
`rate C ≤ Λ_{I_T}(q T)` such that the weight on the interval is at most `fmax_C(window)`. -/
theorem stay_long (A : Interp D) (u : Fin D → Arc) {K : Set (BRel (Fin D))}
    (hK : IsMinIdeal (Mon (B0 A) (B1 A)) K) {E : BRel (Fin D)} (hEK : E ∈ K) (hE : E * E = E)
    {us : Word} (hEus : suppRel (ev A us) = E)
    {w : Word} (hw : IsDigits w) {T : ℕ} (hT : T ≤ w.length) (hmT : us.length ≤ T)
    (hocc : window w (T - us.length) us.length = us)
    {q : ℕ → Fin D} (hp : IsPath u A w T q) {g : ℕ → ℕ}
    (hg : ∀ k < T, A (w.getD k Letter.f) (q k) (q (k + 1)) = Arc.fin (g k))
    {lo n : ℕ} (hlon : lo + n ≤ T) (hreach : Reach (B0 A) (B1 A) (q (lo + n)) (q lo))
    {i : ℕ} (hi1 : lo ≤ i) (hi2 : i + us.length + us.length ≤ lo + n)
    (hwin : window w i us.length = us) :
    ∃ C : Finset (Fin D),
      rate A C ≤ rhoB hE A (hitSet hE (suppV (vecAfter u A (w.take (T - us.length))))) (q T) ∧
      ∑ k ∈ Finset.range n, g (lo + k) ≤ fmax A C (window w lo n) := by
  have hR : ∀ k k', lo ≤ k → k ≤ lo + n → lo ≤ k' → k' ≤ lo + n → Reach (B0 A) (B1 A) (q k) (q k') :=
    fun k k' h1 h2 h3 h4 =>
      (reach_path hw hp h2 hlon).trans (hreach.trans (reach_path hw hp h3 (by omega)))
  obtain ⟨jT, hjT, hbT, hiC⟩ := carry_class A u hK hEK hE hEus hw hT hmT hocc hp (i := i)
    (by omega) hwin (hR _ _ (by omega) (by omega) hi1 (by omega))
  obtain ⟨C, hCr, hCmem⟩ := exists_classRate_eq hE A jT
  refine ⟨C, hCr ▸ le_rhoB hE A hjT hbT, ?_⟩
  have hmemC : ∀ k, lo ≤ k → k ≤ lo + n → q k ∈ C := fun k h1 h2 =>
    (hCmem _).2 (comp_closed hiC (hR i k hi1 (by omega) h1 h2) (hR k i h1 h2 hi1 (by omega)))
  have hle := sum_le_ev_window (restrictI C A) w q g (i := lo) (n := n) (by omega) (fun k hk => by
    simp only [restrictI, hmemC (lo + k) (by omega) (by omega),
      hmemC (lo + k + 1) (by omega) (by omega), and_self, ite_true]
    exact hg (lo + k) (by omega))
  have h1 := natOr0_mono hle
  rw [natOr0_fin] at h1
  exact h1.trans (natOr0_entry_le _ _ _)

end Collatz.Arctic.Upper
