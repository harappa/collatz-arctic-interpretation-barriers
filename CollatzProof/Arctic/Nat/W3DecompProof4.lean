/-
# Natural-number interpretations of 𝒯 (proof of Proposition 12.11, part 4): the recursion of the frozen sums

Tools that unfold the right-hand side of `DecompData.spec` (`termOf`: sum over labels, sum over admissible `(p, r)`, product) one detour at a time.

* **Sums over tuples**: `sum_piFinset_cons` (a sum over `Fin (n+1) → ℕ` is a sum over the head and the rest).
* **Recursion of admissible positions and ranges**: `adm_cons_iff` (`Adm (s+1) t₀ t₁ (p₀ :: p) (r₀ :: r) ⟺ r₀ ≥ 1 ∧ t₀ ≤ p₀ ∧ p₀ + r₀ ≤ t₁ ∧
  Adm s (p₀ + r₀) t₁ p r`) and `sum_admSet_succ`.
* **Parts of the data to be frozen**: the labels `LabT` (`(s_{p_k}, μ(detour word), A_k, starting index of the detour, final index)`),
  the indicator of a long sojourn `thetaInd` (`[Θ(σ, A, σ')_{xy}]`, 0 outside `Q_s`), its chain `thetaChain` (recursion on `s`),
  the condition `firstEnd` on the end of the range, the detour weight `gfun`, and the frozen sum with a general start `frz` (in the form of `termOf`).
* **One step of the recursion** `frz_succ`: `frz (s+1)` is written as a sum over the position, range and label of the first detour of `frz s`.
-/
import CollatzProof.Arctic.Nat.W3DecompProof3

namespace Collatz.Arctic.NatQ5.W3c

open Collatz.Arctic Collatz.Arctic.NatQ5 Matrix
open Collatz.Arctic.MinIdeal (BRel)

set_option linter.unusedSectionVars false

section Tuples

/-- A sum over tuples `Fin (n+1) → ℕ` is a sum over the head and the rest. -/
theorem sum_piFinset_cons {M : Type*} [AddCommMonoid M] {n : ℕ} (S : Finset ℕ) (F : (Fin (n + 1) → ℕ) → M) :
    ∑ f ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S), F f =
      ∑ a ∈ S, ∑ g ∈ Fintype.piFinset (fun _ : Fin n => S), F (Fin.cons a g) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun f => (f 0, Fin.tail f)) (fun ag => Fin.cons ag.1 ag.2) ?_ ?_ ?_ ?_ ?_
  · intro f hf
    rw [Fintype.mem_piFinset] at hf
    exact Finset.mem_product.2 ⟨hf 0, Fintype.mem_piFinset.2 fun i => hf i.succ⟩
  · intro ag hag
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hag
    rw [Fintype.mem_piFinset] at h2 ⊢
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using h1
    · simpa using h2 j
  · intro f _; exact Fin.cons_self_tail f
  · intro ag _; simp
  · intro f _; rw [Fin.cons_self_tail]

/-- Peel off the head of `Adm`. -/
theorem adm_cons_iff (s lb t1 p0 r0 : ℕ) (p r : Fin s → ℕ) :
    Adm (s + 1) lb t1 (Fin.cons p0 p) (Fin.cons r0 r) ↔
      1 ≤ r0 ∧ lb ≤ p0 ∧ p0 + r0 ≤ t1 ∧ Adm s (p0 + r0) t1 p r := by
  unfold Adm
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hr0 : 1 ≤ r0 := by simpa using h1 0
    have hp0 : lb ≤ p0 := by simpa using h2 0 rfl
    have htail1 : ∀ k : Fin s, 1 ≤ r k := fun k => by simpa using h1 k.succ
    have htail2 : ∀ k : Fin s, k.val = 0 → p0 + r0 ≤ p k := fun k hk => by
      have := h3 0 k.succ (by simp [hk])
      simpa using this
    have htail3 : ∀ k k' : Fin s, k'.val = k.val + 1 → p k + r k ≤ p k' := fun k k' hk => by
      have := h3 k.succ k'.succ (by simp [hk])
      simpa using this
    have htail4 : ∀ k : Fin s, k.val + 1 = s → p k + r k ≤ t1 := fun k hk => by
      have := h4 k.succ (by simp [hk])
      simpa using this
    refine ⟨hr0, hp0, ?_, htail1, htail2, htail3, htail4⟩
    rcases Nat.eq_zero_or_pos s with hs | hs
    · have := h4 0 (by simp [hs])
      simpa using this
    · have hadm : Adm s (p0 + r0) t1 p r := ⟨htail1, htail2, htail3, htail4⟩
      have h0 := htail2 ⟨0, hs⟩ rfl
      have := adm_lt hadm ⟨0, hs⟩
      omega
  · rintro ⟨hr0, hp0, hpt, h1, h2, h3, h4⟩
    set P : Fin (s + 1) → ℕ := Fin.cons p0 p with hP
    set Rr : Fin (s + 1) → ℕ := Fin.cons r0 r with hRr
    refine ⟨fun k => ?_, fun k hk => ?_, fun k k' hk => ?_, fun k hk => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) k
      · simpa [hRr] using hr0
      · simpa [hRr] using h1 j
    · have : k = 0 := Fin.ext hk
      subst this; simpa [hP] using hp0
    · revert hk
      refine Fin.cases ?_ (fun j => ?_) k
      · refine Fin.cases ?_ (fun j' => ?_) k'
        · intro h; simp at h
        · intro h
          simp only [hP, hRr, Fin.cons_zero, Fin.cons_succ]
          exact h2 j' (by simpa using h)
      · refine Fin.cases ?_ (fun j' => ?_) k'
        · intro h; simp at h
        · intro h
          simp only [hP, hRr, Fin.cons_succ]
          exact h3 j j' (by simpa using h)
    · revert hk
      refine Fin.cases ?_ (fun j => ?_) k
      · intro _; simpa [hP, hRr] using hpt
      · intro h
        simp only [hP, hRr, Fin.cons_succ]
        exact h4 j (by simpa using h)

open Classical in
/-- The recursion of the sum over admissible `(p, r)`. -/
theorem sum_admSet_succ (s lb t1 N : ℕ) (F : (Fin (s + 1) → ℕ) × (Fin (s + 1) → ℕ) → ℕ) :
    ∑ pr ∈ admSet (s + 1) lb t1 N, F pr =
      ∑ p0 ∈ Finset.range (N + 1), ∑ r0 ∈ Finset.range (N + 1), ind (1 ≤ r0 ∧ lb ≤ p0 ∧ p0 + r0 ≤ t1) *
        ∑ pr ∈ admSet s (p0 + r0) t1 N, F (Fin.cons p0 pr.1, Fin.cons r0 pr.2) := by
  have hfilt : ∀ (n t0 : ℕ) (G : (Fin n → ℕ) × (Fin n → ℕ) → ℕ), ∑ pr ∈ admSet n t0 t1 N, G pr =
      ∑ p ∈ Fintype.piFinset (fun _ : Fin n => Finset.range (N + 1)),
        ∑ r ∈ Fintype.piFinset (fun _ : Fin n => Finset.range (N + 1)), ind (Adm n t0 t1 p r) * G (p, r) := by
    intro n t0 G
    unfold admSet
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
    unfold ind
    split_ifs <;> simp
  rw [hfilt, sum_piFinset_cons]
  refine Finset.sum_congr rfl fun p0 _ => ?_
  simp_rw [sum_piFinset_cons (n := s) (Finset.range (N + 1))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r0 _ => ?_
  rw [hfilt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [adm_cons_iff, show (1 ≤ r0 ∧ lb ≤ p0 ∧ p0 + r0 ≤ t1 ∧ Adm s (p0 + r0) t1 p r) ↔
    ((1 ≤ r0 ∧ lb ≤ p0 ∧ p0 + r0 ≤ t1) ∧ Adm s (p0 + r0) t1 p r) by tauto, ind_and]
  ring

end Tuples

section Data

/-- The finite-type structure of `BRel (ZIdx A)` (from `Finite`; not computed). -/
@[reducible] noncomputable def fintypeBRelZ {Q : Type} [Fintype Q] [DecidableEq Q] {A : ValAuto Q} :
    Fintype (BRel (ZIdx A)) :=
  Fintype.ofFinite _

attribute [local instance] fintypeBRelZ

variable {Q : Type} [Fintype Q] [DecidableEq Q] (A : ValAuto Q) (u : List (Fin 2)) (e : BRel (ZIdx A))

/-- **Labels**: `(s_{p_k}, μ(ω_{(p_k,p'_k]}), A_k = μ(ω_{(p'_k,r_k]}), starting index of the detour, final index)`. -/
abbrev LabT := BRel (ZIdx A) × BRel (ZIdx A) × BRel (ZIdx A) × Q × Q

/-- The indicator of a long sojourn `[Θ(σ, A, σ')_{xy}]` (only when `x, y ∈ Q_s`). -/
noncomputable def thetaInd (σ Am σ' : BRel (ZIdx A)) (x y : Q) : ℕ :=
  ind (∃ hx : InZ A x, ∃ hy : InZ A y, theta e σ Am σ' ⟨x, hx⟩ ⟨y, hy⟩)

/-- The chain of indicators of long sojourns (the core of `κ`). The last long sojourn ends at `s_T` and reaches the index `j₁`. -/
noncomputable def thetaChain (sT : BRel (ZIdx A)) (j1 : Q) :
    (s : ℕ) → BRel (ZIdx A) → BRel (ZIdx A) → Q → (Fin s → LabT A) → ℕ
  | 0, σ, Am, x, _ => thetaInd A e σ Am sT x j1
  | s + 1, σ, Am, x, l => thetaInd A e σ Am (l 0).1 x (l 0).2.2.2.1 *
      thetaChain sT j1 s ((l 0).1 * (l 0).2.1) (l 0).2.2.1 (l 0).2.2.2.2 (Fin.tail l)

/-- The first occurrence of `u♯` that starts at or after the position `a` of the window `v` ends exactly at the end of the window. -/
def firstEnd (v : List (Fin 2)) (a : ℕ) : Prop :=
  u <:+: v.drop a ∧ ¬ u <:+: (v.drop a).take (v.length - a - 1)

/-- **Detour weight** (range exactly `r`, window `v`): for the end `a` of the detour (a position in the window), the entry of the detour kernel `detW`,
multiplied by the agreement with the label and by the condition on the end of the range. -/
noncomputable def gfun (l : LabT A) (r : ℕ) (v : List (Fin 2)) : ℕ :=
  ind (v.length = r ∧ Rel A l.2.2.2.1 ∧ Rel A l.2.2.2.2) *
    ∑ a ∈ Finset.range r, ind (1 ≤ a ∧ l.2.1 = muZ A (v.take a) ∧ l.2.2.1 = muZ A (v.drop a) ∧ firstEnd u v a) *
      detW A u (v.take a) l.2.2.2.1 l.2.2.2.2

/-- The frozen sum with a general start (in the form of `termOf`). -/
noncomputable def frz (ω : List (Fin 2)) (t1 : ℕ) (sT : BRel (ZIdx A)) (j1 : Q) (s lb : ℕ)
    (σ Am : BRel (ZIdx A)) (x : Q) : ℕ :=
  termOf A Prod.fst s (fun sT' l => thetaChain A e sT' j1 s σ Am x l) (fun _ => gfun A u) lb t1 sT ω

/-- A sum over `Fin (n+1) → α` is a sum over the head and the rest. -/
theorem sum_fin_succ_fun {α M : Type*} [Fintype α] [AddCommMonoid M] {n : ℕ} (F : (Fin (n + 1) → α) → M) :
    ∑ f, F f = ∑ a, ∑ g : Fin n → α, F (Fin.cons a g) := by
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  rfl

/-- Exchange the outer two and the inner two of a fourfold sum. -/
theorem sum_swap_12_34 {α β γ δ M : Type*} [AddCommMonoid M] (S : Finset α) (T : Finset β) (U : Finset γ)
    (V : Finset δ) (f : α → β → γ → δ → M) :
    ∑ a ∈ S, ∑ b ∈ T, ∑ c ∈ U, ∑ d ∈ V, f a b c d = ∑ c ∈ U, ∑ d ∈ V, ∑ a ∈ S, ∑ b ∈ T, f a b c d := by
  calc ∑ a ∈ S, ∑ b ∈ T, ∑ c ∈ U, ∑ d ∈ V, f a b c d
      = ∑ a ∈ S, ∑ c ∈ U, ∑ b ∈ T, ∑ d ∈ V, f a b c d := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c ∈ U, ∑ a ∈ S, ∑ b ∈ T, ∑ d ∈ V, f a b c d := Finset.sum_comm
    _ = ∑ c ∈ U, ∑ a ∈ S, ∑ d ∈ V, ∑ b ∈ T, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c ∈ U, ∑ d ∈ V, ∑ a ∈ S, ∑ b ∈ T, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- **One step of the recursion**. -/
theorem frz_succ (ω : List (Fin 2)) (t1 : ℕ) (sT : BRel (ZIdx A)) (j1 : Q) (s lb : ℕ)
    (σ Am : BRel (ZIdx A)) (x : Q) :
    frz A u e ω t1 sT j1 (s + 1) lb σ Am x =
      ∑ p0 ∈ Finset.range (ω.length + 1), ∑ r0 ∈ Finset.range (ω.length + 1),
        ind (1 ≤ r0 ∧ lb ≤ p0 ∧ p0 + r0 ≤ t1) *
          ∑ l0 : LabT A, thetaInd A e σ Am l0.1 x l0.2.2.2.1 * xiOf A Prod.fst (gfun A u) l0 r0 ω p0 *
            frz A u e ω t1 sT j1 s (p0 + r0) (l0.1 * l0.2.1) l0.2.2.1 l0.2.2.2.2 := by
  unfold frz termOf
  rw [sum_fin_succ_fun]
  have hchain : ∀ (l0 : LabT A) (l' : Fin s → LabT A),
      thetaChain A e sT j1 (s + 1) σ Am x (Fin.cons l0 l') =
        thetaInd A e σ Am l0.1 x l0.2.2.2.1 * thetaChain A e sT j1 s (l0.1 * l0.2.1) l0.2.2.1 l0.2.2.2.2 l' := by
    intro l0 l'
    simp only [thetaChain, Fin.cons_zero, Fin.tail_cons]
  have hprod : ∀ (l0 : LabT A) (l' : Fin s → LabT A) (p0 r0 : ℕ) (pr : (Fin s → ℕ) × (Fin s → ℕ)),
      ∏ k : Fin (s + 1), xiOf A Prod.fst (gfun A u) ((Fin.cons l0 l' : Fin (s + 1) → LabT A) k)
          ((Fin.cons r0 pr.2 : Fin (s + 1) → ℕ) k) ω ((Fin.cons p0 pr.1 : Fin (s + 1) → ℕ) k) =
        xiOf A Prod.fst (gfun A u) l0 r0 ω p0 *
          ∏ k : Fin s, xiOf A Prod.fst (gfun A u) (l' k) (pr.2 k) ω (pr.1 k) := by
    intro l0 l' p0 r0 pr
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
  simp_rw [hchain, sum_admSet_succ, hprod]
  -- exchange the order of summation
  simp only [Finset.mul_sum]
  rw [sum_swap_12_34]
  refine Finset.sum_congr rfl fun p0 _ => Finset.sum_congr rfl fun r0 _ => Finset.sum_congr rfl fun l0 _ =>
    Finset.sum_congr rfl fun l' _ => Finset.sum_congr rfl fun pr _ => ?_
  ring

/-- Collapsing the sum over labels: the components state, type of the detour word and type of the tail of the range are determined by the indicators. -/
theorem label_collapse (ω : List (Fin 2)) (p0 r0 : ℕ) (σ Am : BRel (ZIdx A)) (x : Q) (G : LabT A → ℕ) :
    ∑ l0 : LabT A, thetaInd A e σ Am l0.1 x l0.2.2.2.1 * xiOf A Prod.fst (gfun A u) l0 r0 ω p0 * G l0 =
      ∑ a ∈ Finset.range r0, ∑ k, ∑ i',
        ind (((ω.drop p0).take r0).length = r0 ∧ Rel A k ∧ Rel A i') *
          ind (1 ≤ a ∧ firstEnd u ((ω.drop p0).take r0) a) *
          (thetaInd A e σ Am (muZ A (ω.take p0)) x k * detW A u (((ω.drop p0).take r0).take a) k i' *
            G (muZ A (ω.take p0), muZ A (((ω.drop p0).take r0).take a), muZ A (((ω.drop p0).take r0).drop a), k, i')) := by
  unfold xiOf gfun
  set v := (ω.drop p0).take r0
  set s0 := muZ A (ω.take p0)
  have hsplit : ∀ (l0 : LabT A), thetaInd A e σ Am l0.1 x l0.2.2.2.1 *
      (ind (s0 = l0.1) * (ind (v.length = r0 ∧ Rel A l0.2.2.2.1 ∧ Rel A l0.2.2.2.2) *
        ∑ a ∈ Finset.range r0, ind (1 ≤ a ∧ l0.2.1 = muZ A (v.take a) ∧ l0.2.2.1 = muZ A (v.drop a) ∧ firstEnd u v a) *
          detW A u (v.take a) l0.2.2.2.1 l0.2.2.2.2)) * G l0 =
      ∑ a ∈ Finset.range r0, ind (l0.1 = s0) * (ind (l0.2.1 = muZ A (v.take a)) * (ind (l0.2.2.1 = muZ A (v.drop a)) *
        (ind (v.length = r0 ∧ Rel A l0.2.2.2.1 ∧ Rel A l0.2.2.2.2) * ind (1 ≤ a ∧ firstEnd u v a) *
          (thetaInd A e σ Am l0.1 x l0.2.2.2.1 * detW A u (v.take a) l0.2.2.2.1 l0.2.2.2.2 * G l0)))) := by
    intro l0
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h1 : ind (1 ≤ a ∧ l0.2.1 = muZ A (v.take a) ∧ l0.2.2.1 = muZ A (v.drop a) ∧ firstEnd u v a) =
        ind (l0.2.1 = muZ A (v.take a)) * (ind (l0.2.2.1 = muZ A (v.drop a)) * ind (1 ≤ a ∧ firstEnd u v a)) := by
      rw [show (1 ≤ a ∧ l0.2.1 = muZ A (v.take a) ∧ l0.2.2.1 = muZ A (v.drop a) ∧ firstEnd u v a) ↔
        (l0.2.1 = muZ A (v.take a) ∧ l0.2.2.1 = muZ A (v.drop a) ∧ (1 ≤ a ∧ firstEnd u v a)) by tauto,
        ind_and, ind_and]
    have h2 : ind (s0 = l0.1) = ind (l0.1 = s0) := by
      rw [show (s0 = l0.1) = (l0.1 = s0) from propext eq_comm]
    rw [h1, h2]
    ac_rfl
  simp_rw [hsplit]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  -- split into sums over the components of the label and collapse the state, the type of the word and the type of the tail
  simp only [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single s0, Fintype.sum_eq_single (muZ A (v.take a)), Fintype.sum_eq_single (muZ A (v.drop a))]
  · refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i' _ => ?_
    rw [ind_pos rfl, ind_pos rfl, ind_pos rfl]
    simp only [one_mul]
  · intro A0 hA0
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun i' _ => ?_
    rw [ind_neg hA0]; simp
  · intro P0 hP0
    refine Finset.sum_eq_zero fun A0 _ => Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun i' _ => ?_
    rw [ind_neg hP0]; simp
  · intro σ0 hσ0
    refine Finset.sum_eq_zero fun P0 _ => Finset.sum_eq_zero fun A0 _ => Finset.sum_eq_zero fun k _ =>
      Finset.sum_eq_zero fun i' _ => ?_
    rw [ind_neg hσ0]; simp

end Data

end Collatz.Arctic.NatQ5.W3c
