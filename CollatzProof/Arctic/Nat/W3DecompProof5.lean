/-
# Natural-number interpretations of 𝒯 (proof of Proposition 12.11, part 5): the frozen sums agree with the chains

For a general start `y` (the start of a long sojourn, `y ≤ t_m`), the frozen sum `frz` (sum over labels and over admissible `(p, r)`) equals the chain `LFs`;
this is shown by induction on the number of detours (`frz_eq`).

* Facts on positions: the window `(ω.drop p).take r = ω_{(p,p+r]}`, `firstEnd ⟺ firstOcc + |u♯| = p + r` (`firstEnd_iff`),
  and the indicator of `Θ` is the weight of a long sojourn (`thetaInd_of_eq`, `theta_long`).
* One step of `LFs` is rewritten as a sum over the ranges of the position `p₀` and of the length `a` of the detour (`LFs_succ_range`).
* Agreement term by term (`term_eq`): the range `r₀` is uniquely determined as `firstOcc(p₀ + a) + |u♯| − p₀`.
-/
import CollatzProof.Arctic.Nat.W3DecompProof4

namespace Collatz.Arctic.NatQ5.W3c

open Collatz.Arctic Collatz.Arctic.NatQ5 Matrix
open Collatz.Arctic.MinIdeal (BRel)

set_option linter.unusedSectionVars false

attribute [local instance] fintypeBRelZ

section Pos

theorem window_eq_seg (ω : List (Fin 2)) (p r : ℕ) : (ω.drop p).take r = seg ω p (p + r) := by
  simp [seg]

theorem infix_seg_iff' (u ω : List (Fin 2)) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ ω.length) :
    u <:+: seg ω a b ↔ firstOcc u ω a + u.length ≤ b := infix_seg_iff_firstOcc u ω hab hb

theorem firstEnd_iff (u ω : List (Fin 2)) {p r a : ℕ} (hN : p + r ≤ ω.length) (ha : a < r) :
    firstEnd u ((ω.drop p).take r) a ↔ firstOcc u ω (p + a) + u.length = p + r := by
  unfold firstEnd
  rw [window_eq_seg, length_seg ω hN, seg_drop, show p + r - p - a - 1 = (p + r - 1) - (p + a) by omega,
    seg_take ω (p + a) (p + r) _ (by omega), show p + a + (p + r - 1 - (p + a)) = p + r - 1 by omega,
    infix_seg_iff' u ω (by omega) hN, infix_seg_iff' u ω (by omega) (by omega)]
  omega

end Pos

section Theta

variable {Q : Type} [Fintype Q] [DecidableEq Q] (A : ValAuto Q) {u : List (Fin 2)} {K : Set (BRel (ZIdx A))}
  {e : BRel (ZIdx A)}

/-- If `Θ` is the type of a word, its indicator is the weight of a long sojourn. -/
theorem thetaInd_of_eq {σ Am σ' : BRel (ZIdx A)} {w : List (Fin 2)} (h : theta e σ Am σ' = muZ A w) (x y : Q) :
    thetaInd A e σ Am σ' x y = ind (InZ A x) * Rigid.DxN (Dp A) w x y := by
  unfold thetaInd
  rw [h]
  by_cases hx : InZ A x
  · rw [ind_pos hx, one_mul, DxN_Dp]
    by_cases hy : y ∈ sccOf A x
    · have hyz : InZ A y := inZ_of_mem A hx hy
      simp only [hy, ↓reduceIte]
      rw [DxN_eq_ite_muZ A (x := ⟨x, hx⟩) (y := ⟨y, hyz⟩) hy w]
      by_cases hm : muZ A w ⟨x, hx⟩ ⟨y, hyz⟩
      · rw [ind_pos ⟨hx, hyz, hm⟩]; simp only [hm, ↓reduceIte]
      · rw [ind_neg (fun ⟨_, _, h'⟩ => hm h')]; simp only [hm, ↓reduceIte]
    · simp only [hy, ↓reduceIte]
      rw [ind_neg]
      rintro ⟨_, _, h'⟩
      exact hy h'.1
  · rw [ind_neg hx, zero_mul, ind_neg]
    rintro ⟨h', _⟩
    exact hx h'

variable (hS : Sharp A K u e)
include hS

/-- For a long sojourn (the first occurrence at or after `y` ends by `q`), `Θ(s_y, A_y, s_q) = μ(ω_{(y,q]})`. -/
theorem theta_long (ω : List (Fin 2)) {y q : ℕ}
    (hex : ∃ i, y ≤ i ∧ occAt u ω i) (hlong : firstOcc u ω y + u.length ≤ q) :
    theta e (muZ A (ω.take y)) (muZ A (seg ω y (firstOcc u ω y + u.length))) (muZ A (ω.take q)) =
      muZ A (seg ω y q) := by
  obtain ⟨h1, h2⟩ := firstOcc_spec hex
  exact (theta_spec A hS ω h1 hlong h2).symm

end Theta

section Main

variable {Q : Type} [Fintype Q] [DecidableEq Q] {A : ValAuto Q} {u : List (Fin 2)} {K : Set (BRel (ZIdx A))}
  {e : BRel (ZIdx A)} {ω : List (Fin 2)} {tm : ℕ} {j1 : Q}

/-- The last copy is an occurrence. -/
theorem occ_last (hcopy : seg ω tm (tm + u.length) = u) (hN : tm + u.length ≤ ω.length) : occAt u ω tm := by
  refine ⟨hN, ?_⟩
  have : seg ω tm (tm + u.length) = (ω.drop tm).take u.length := by simp [seg]
  rw [← this, hcopy]

theorem firstOcc_le_tm (hcopy : seg ω tm (tm + u.length) = u) (hN : tm + u.length ≤ ω.length) {y : ℕ}
    (hy : y ≤ tm) : firstOcc u ω y ≤ tm :=
  firstOcc_le hy (occ_last hcopy hN)

theorem exists_occ (hcopy : seg ω tm (tm + u.length) = u) (hN : tm + u.length ≤ ω.length) {y : ℕ}
    (hy : y ≤ tm) : ∃ i, y ≤ i ∧ occAt u ω i := ⟨tm, hy, occ_last hcopy hN⟩

theorem muZ_take_seg (A : ValAuto Q) (ω : List (Fin 2)) {p x : ℕ} (hpx : p ≤ x) :
    muZ A (ω.take p) * muZ A (seg ω p x) = muZ A (ω.take x) := by
  rw [← muZ_append, take_split ω hpx]; rfl

/-- Rewrite one step of `LFs` as a sum over the ranges of the position `p₀` and of the length `a` of the detour (`x' = p₀ + a`). -/
theorem LFs_succ_range (hN : tm + u.length ≤ ω.length) (s y : ℕ) (x : Q) :
    LFs A u ω tm j1 (s + 1) y x =
      ∑ p0 ∈ Finset.range (ω.length + 1), ∑ a ∈ Finset.range (ω.length + 1), ∑ k, ∑ i',
        ind (InZ A x ∧ y ≤ p0 ∧ u <:+: seg ω y p0 ∧ 1 ≤ a ∧ p0 + a ≤ tm ∧ Rel A k ∧ Rel A i') *
          (Rigid.DxN (Dp A) (seg ω y p0) x k * detW A u (seg ω p0 (p0 + a)) k i' *
            LFs A u ω tm j1 s (p0 + a) i') := by
  rw [LFs_succ]
  -- the sum over the position `q`
  rw [← sum_ind_eq (s := Finset.Ico y tm) (t := Finset.range (ω.length + 1)) (P := fun p0 => y ≤ p0 ∧ p0 < tm) _
    (fun q hq => Finset.mem_range.2 (by have := Finset.mem_Ico.1 hq; omega)) (fun q _ => by rw [Finset.mem_Ico])]
  refine Finset.sum_congr rfl fun p0 _ => ?_
  -- replace `x'` by `p₀ + a`
  have hx' : ∀ (f : ℕ → ℕ), ∑ x' ∈ Finset.Icc (p0 + 1) tm, f x' =
      ∑ a ∈ Finset.range (ω.length + 1), ind (1 ≤ a ∧ p0 + a ≤ tm) * f (p0 + a) := by
    intro f
    rw [sum_ind_eq (P := fun a => 1 ≤ a ∧ p0 + a ≤ tm) (s := Finset.Icc 1 (tm - p0)) (fun a => f (p0 + a))
      (fun a ha => Finset.mem_range.2 (by have := Finset.mem_Icc.1 ha; omega))
      (fun a _ => by rw [Finset.mem_Icc]; omega)]
    refine Finset.sum_nbij' (fun x' => x' - p0) (fun a => p0 + a) ?_ ?_ ?_ ?_ ?_
    · intro x' hx'; have := Finset.mem_Icc.1 hx'; exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    · intro a ha; have := Finset.mem_Icc.1 ha; exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    · intro x' hx'; have := Finset.mem_Icc.1 hx'; omega
    · intro a ha; omega
    · intro x' hx'; have := Finset.mem_Icc.1 hx'; congr 1; omega
  simp_rw [hx']
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i' _ => ?_
  -- combine the indicators
  by_cases hc : InZ A x ∧ y ≤ p0 ∧ u <:+: seg ω y p0 ∧ 1 ≤ a ∧ p0 + a ≤ tm ∧ Rel A k ∧ Rel A i'
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hc
    rw [ind_pos (⟨h1, h2, h3, h4, h5, h6, h7⟩ : InZ A x ∧ y ≤ p0 ∧ u <:+: seg ω y p0 ∧ 1 ≤ a ∧ p0 + a ≤ tm ∧
      Rel A k ∧ Rel A i'), ind_pos (⟨h2, by omega⟩ : y ≤ p0 ∧ p0 < tm), ind_pos (⟨h4, h5⟩ : 1 ≤ a ∧ p0 + a ≤ tm),
      ind_pos (⟨h1, h3, h6, h7⟩ : InZ A x ∧ u <:+: seg ω y p0 ∧ Rel A k ∧ Rel A i')]
    simp only [one_mul]
  · rw [ind_neg hc, zero_mul]
    by_cases hp : y ≤ p0 ∧ p0 < tm
    · by_cases ha : 1 ≤ a ∧ p0 + a ≤ tm
      · rw [ind_neg (P := InZ A x ∧ u <:+: seg ω y p0 ∧ Rel A k ∧ Rel A i')
          (fun h => hc ⟨h.1, hp.1, h.2.1, ha.1, ha.2, h.2.2.1, h.2.2.2⟩)]; simp
      · rw [ind_neg (P := 1 ≤ a ∧ p0 + a ≤ tm) ha]; simp
    · rw [ind_neg (P := y ≤ p0 ∧ p0 < tm) hp]; simp

theorem length_window {p r : ℕ} (hp : p ≤ ω.length) : ((ω.drop p).take r).length = r ↔ p + r ≤ ω.length := by
  simp only [List.length_take, List.length_drop]; omega

variable (h01 : ∀ C, IsComp A C → ZeroOne A C) (hS : Sharp A K u e) (hcopy : seg ω tm (tm + u.length) = u)
  (hN : tm + u.length ≤ ω.length)
include h01 hS hcopy hN

/-- **Agreement term by term**: the range `r₀` is uniquely determined as `firstOcc(p₀ + a) + |u♯| − p₀`, and then the term is the term of the chain. -/
theorem term_eq (s y : ℕ) (x : Q) (hy : y ≤ tm)
    (ih : ∀ (y : ℕ) (x : Q), y ≤ tm →
      frz A u e ω (tm + u.length) (muZ A (ω.take (tm + u.length))) j1 s (firstOcc u ω y + u.length)
        (muZ A (ω.take y)) (muZ A (seg ω y (firstOcc u ω y + u.length))) x = LFs A u ω tm j1 s y x)
    (p0 r0 a : ℕ) (k i' : Q) (hp0 : p0 ≤ ω.length) (ha : a < r0) :
    ind (1 ≤ r0 ∧ firstOcc u ω y + u.length ≤ p0 ∧ p0 + r0 ≤ tm + u.length) *
      (ind (((ω.drop p0).take r0).length = r0 ∧ Rel A k ∧ Rel A i') *
        ind (1 ≤ a ∧ firstEnd u ((ω.drop p0).take r0) a) *
        (thetaInd A e (muZ A (ω.take y)) (muZ A (seg ω y (firstOcc u ω y + u.length))) (muZ A (ω.take p0)) x k *
          detW A u (((ω.drop p0).take r0).take a) k i' *
          frz A u e ω (tm + u.length) (muZ A (ω.take (tm + u.length))) j1 s (p0 + r0)
            (muZ A (ω.take p0) * muZ A (((ω.drop p0).take r0).take a)) (muZ A (((ω.drop p0).take r0).drop a)) i')) =
      ind (r0 = firstOcc u ω (p0 + a) + u.length - p0) *
        (ind (InZ A x ∧ y ≤ p0 ∧ u <:+: seg ω y p0 ∧ 1 ≤ a ∧ p0 + a ≤ tm ∧ Rel A k ∧ Rel A i') *
          (Rigid.DxN (Dp A) (seg ω y p0) x k * detW A u (seg ω p0 (p0 + a)) k i' *
            LFs A u ω tm j1 s (p0 + a) i')) := by
  have hyo : y ≤ firstOcc u ω y := (firstOcc_spec (exists_occ hcopy hN hy)).1
  by_cases hc : (1 ≤ r0 ∧ firstOcc u ω y + u.length ≤ p0 ∧ p0 + r0 ≤ tm + u.length) ∧
      (((ω.drop p0).take r0).length = r0 ∧ Rel A k ∧ Rel A i') ∧ (1 ≤ a ∧ firstEnd u ((ω.drop p0).take r0) a)
  · obtain ⟨⟨hr1, hlong, hpt⟩, ⟨hlen, hk, hi'⟩, ⟨ha1, hfe⟩⟩ := hc
    have hpN : p0 + r0 ≤ ω.length := (length_window hp0).1 hlen
    have hfo : firstOcc u ω (p0 + a) + u.length = p0 + r0 := (firstEnd_iff u ω hpN ha).1 hfe
    have hex' : ∃ i, p0 + a ≤ i ∧ occAt u ω i := by
      have h1 := hfe.1
      rw [window_eq_seg, seg_drop] at h1
      obtain ⟨i, hi1, -, hi3⟩ := (infix_seg_iff u ω (by omega) hpN).1 h1
      exact ⟨i, hi1, hi3⟩
    have hx'o : p0 + a ≤ firstOcc u ω (p0 + a) := (firstOcc_spec hex').1
    have hx'tm : p0 + a ≤ tm := by omega
    have hyp : y ≤ p0 := by omega
    have hinf : u <:+: seg ω y p0 := (infix_seg_iff' u ω hyp hp0).2 hlong
    rw [ind_pos ⟨hr1, hlong, hpt⟩, ind_pos ⟨hlen, hk, hi'⟩, ind_pos ⟨ha1, hfe⟩, ind_pos (show r0 =
      firstOcc u ω (p0 + a) + u.length - p0 by omega)]
    -- `Θ` is the weight of a long sojourn
    rw [thetaInd_of_eq A (theta_long A hS ω (exists_occ hcopy hN hy) hlong) x k]
    -- the window as an interval word
    rw [window_eq_seg, seg_take ω p0 (p0 + r0) a (by omega), seg_drop, muZ_take_seg A ω (show p0 ≤ p0 + a by omega)]
    -- the induction hypothesis
    rw [show p0 + r0 = firstOcc u ω (p0 + a) + u.length by omega, ih (p0 + a) i' hx'tm]
    by_cases hx : InZ A x
    · rw [ind_pos hx, ind_pos ⟨hx, hyp, hinf, ha1, hx'tm, hk, hi'⟩]; ring
    · rw [ind_neg hx, ind_neg (fun h => hx h.1)]; ring
  · -- the left-hand side vanishes
    have hL : ind (1 ≤ r0 ∧ firstOcc u ω y + u.length ≤ p0 ∧ p0 + r0 ≤ tm + u.length) *
        (ind (((ω.drop p0).take r0).length = r0 ∧ Rel A k ∧ Rel A i') *
          ind (1 ≤ a ∧ firstEnd u ((ω.drop p0).take r0) a)) = 0 := by
      rw [← ind_and, ← ind_and, ind_neg hc]
    have hL' : ∀ X : ℕ, ind (1 ≤ r0 ∧ firstOcc u ω y + u.length ≤ p0 ∧ p0 + r0 ≤ tm + u.length) *
        (ind (((ω.drop p0).take r0).length = r0 ∧ Rel A k ∧ Rel A i') *
          ind (1 ≤ a ∧ firstEnd u ((ω.drop p0).take r0) a) * X) = 0 := by
      intro X; rw [← mul_assoc, hL, zero_mul]
    rw [hL']
    -- the right-hand side vanishes as well
    by_cases hr : r0 = firstOcc u ω (p0 + a) + u.length - p0
    · by_cases hpsi : InZ A x ∧ y ≤ p0 ∧ u <:+: seg ω y p0 ∧ 1 ≤ a ∧ p0 + a ≤ tm ∧ Rel A k ∧ Rel A i'
      · exfalso
        obtain ⟨_, hyp, hinf, ha1, hx'tm, hk, hi'⟩ := hpsi
        have hfo1 := firstOcc_le_tm hcopy hN hx'tm
        have hfo2 := (firstOcc_spec (exists_occ hcopy hN hx'tm)).1
        have hpN : p0 + r0 ≤ ω.length := by omega
        refine hc ⟨⟨by omega, (infix_seg_iff' u ω hyp hp0).1 hinf, by omega⟩, ⟨(length_window hp0).2 hpN, hk, hi'⟩,
          ⟨ha1, (firstEnd_iff u ω hpN ha).2 (by omega)⟩⟩
      · rw [ind_neg hpsi]; simp
    · rw [ind_neg hr]; simp

/-- **Agreement**: the frozen sum from a long sojourn starting at `y ≤ t_m` equals the chain. -/
theorem frz_eq : ∀ (s y : ℕ) (x : Q), y ≤ tm →
    frz A u e ω (tm + u.length) (muZ A (ω.take (tm + u.length))) j1 s (firstOcc u ω y + u.length)
        (muZ A (ω.take y)) (muZ A (seg ω y (firstOcc u ω y + u.length))) x =
      LFs A u ω tm j1 s y x := by
  intro s
  induction s with
  | zero =>
    intro y x hy
    unfold frz
    rw [termOf_of_deg_zero A _ rfl]
    simp only [thetaChain]
    rw [thetaInd_of_eq A (theta_long A hS ω (exists_occ hcopy hN hy)
      (by have := firstOcc_le_tm hcopy hN hy; omega)) x j1, LFs_zero]
  | succ s ih =>
    intro y x hy
    rw [frz_succ, LFs_succ_range hN]
    refine Finset.sum_congr rfl fun p0 hp0 => ?_
    have hp0N : p0 ≤ ω.length := by have := Finset.mem_range.1 hp0; omega
    -- collapse the labels
    have hlc : ∀ r0, ∑ l0 : LabT A, thetaInd A e (muZ A (ω.take y)) (muZ A (seg ω y (firstOcc u ω y + u.length)))
          l0.1 x l0.2.2.2.1 * xiOf A Prod.fst (gfun A u) l0 r0 ω p0 *
          frz A u e ω (tm + u.length) (muZ A (ω.take (tm + u.length))) j1 s (p0 + r0) (l0.1 * l0.2.1) l0.2.2.1
            l0.2.2.2.2 =
        ∑ a ∈ Finset.range r0, ∑ k, ∑ i',
          ind (((ω.drop p0).take r0).length = r0 ∧ Rel A k ∧ Rel A i') *
            ind (1 ≤ a ∧ firstEnd u ((ω.drop p0).take r0) a) *
            (thetaInd A e (muZ A (ω.take y)) (muZ A (seg ω y (firstOcc u ω y + u.length))) (muZ A (ω.take p0)) x k *
              detW A u (((ω.drop p0).take r0).take a) k i' *
              frz A u e ω (tm + u.length) (muZ A (ω.take (tm + u.length))) j1 s (p0 + r0)
                (muZ A (ω.take p0) * muZ A (((ω.drop p0).take r0).take a))
                (muZ A (((ω.drop p0).take r0).drop a)) i') := fun r0 =>
      label_collapse A u e ω p0 r0 _ _ x
        (fun l0 => frz A u e ω (tm + u.length) (muZ A (ω.take (tm + u.length))) j1 s (p0 + r0)
          (l0.1 * l0.2.1) l0.2.2.1 l0.2.2.2.2)
    simp_rw [hlc, Finset.mul_sum]
    -- agreement term by term
    rw [Finset.sum_congr rfl fun r0 _ => Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun i' _ =>
        term_eq h01 hS hcopy hN s y x hy ih p0 r0 a k i' hp0N (Finset.mem_range.1 ha)]
    -- exchange `r₀` and `a`, and collapse `r₀`
    rw [Finset.sum_comm' (t' := Finset.range (ω.length + 1))
      (s' := fun a => (Finset.range (ω.length + 1)).filter (a < ·))
      (fun r0 a => by simp only [Finset.mem_range, Finset.mem_filter]; omega)]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i' _ => ?_
    by_cases hpa : p0 + a ≤ tm
    · have hfo1 := firstOcc_le_tm hcopy hN hpa
      have hfo2 := (firstOcc_spec (exists_occ hcopy hN hpa)).1
      rw [Finset.sum_eq_single (firstOcc u ω (p0 + a) + u.length - p0)]
      · rw [ind_pos rfl, one_mul]
      · intro r0 _ hne; rw [ind_neg hne, zero_mul]
      · intro hn; exfalso; apply hn
        simp only [Finset.mem_filter, Finset.mem_range]
        have hL : 1 ≤ u.length := List.length_pos_iff.2 hS.ne_nil
        omega
    · rw [ind_neg (P := InZ A x ∧ y ≤ p0 ∧ u <:+: seg ω y p0 ∧ 1 ≤ a ∧ p0 + a ≤ tm ∧ Rel A k ∧ Rel A i')
        (fun h => hpa h.2.2.2.2.1)]
      simp

end Main

end Collatz.Arctic.NatQ5.W3c
