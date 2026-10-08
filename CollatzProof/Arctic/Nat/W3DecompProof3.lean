/-
# Natural-number interpretations of 𝒯 (proof of Proposition 12.11, part 3): cutting at the top part and at the low part

The sum over the sets of crossing positions (`DxN_add_eq_sum`) is split by the **first unbroken copy** among the copies of `(u♯)^R` (top part, `t₀`)
and by the **last unbroken copy** (shared part, `t₁`). A term in which every copy is broken vanishes, since `|P| ≥ R ≥ |Q|`.

* `mix_block`: the sum of the terms without crossing positions in `[a, a + L)` is the product of the sum for the part before, `D_{ω_{(a,a+L]}}` and the sum for the part after
  (the conditions before and after are arbitrary predicates).
* `copy_seg`: the copy `c` of `α (u♯)^R β` is `u♯`.
* `block_first`: `B_w = Σ_{c < R} U_c D_{u♯} B_{w_{>a_c+L}}`, where `U_c` is the sum for the part before with "every copy `c' < c` is broken".
* `block_last`: `B_w = Σ_{c < R} B_{w_{≤a_c}} D_{u♯} W_c`, where `W_c` is the sum for the part after with "every copy `c' > c` is broken".
-/
import CollatzProof.Arctic.Nat.W3DecompProof2

namespace Collatz.Arctic.NatQ5.W3c

open Collatz.Arctic Collatz.Arctic.NatQ5 Matrix
open Collatz.Arctic.MinIdeal (BRel)

set_option linter.unusedSectionVars false

section Block

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (A : ValAuto Q)

/-- **Splitting at an interval**: the sum of the terms without crossing positions in `[a, a + L)` is the product of the parts before, in the middle and after (the elements of `S` are
the sets of crossing positions whose part before lies in `S₁` and whose part after lies in `S₂`). -/
theorem mix_block (w : List (Fin 2)) {a L : ℕ} (haL : a + L ≤ w.length) (S S1 S2 : Finset (Finset ℕ))
    (hS1 : ∀ P ∈ S1, P ⊆ Finset.range a) (hS2 : ∀ P ∈ S2, P ⊆ Finset.Ico (a + L) w.length)
    (hS : ∀ P, P ∈ S ↔ P ⊆ Finset.range w.length ∧ (∀ p ∈ P, ¬ (a ≤ p ∧ p < a + L)) ∧
      P.filter (· < a) ∈ S1 ∧ P.filter (a + L ≤ ·) ∈ S2) :
    ∑ P ∈ S, mixAux (Dp A) (Ep A) P 0 w =
      (∑ P1 ∈ S1, mixAux (Dp A) (Ep A) P1 0 (w.take a)) * Rigid.DxN (Dp A) (seg w a (a + L)) *
        (∑ P2 ∈ S2, mixAux (Dp A) (Ep A) P2 (a + L) (w.drop (a + L))) := by
  rw [Finset.sum_mul, Finset.sum_mul_sum, ← Finset.sum_product']
  have hw : w = w.take a ++ (seg w a (a + L) ++ w.drop (a + L)) := by
    have : seg w a (a + L) ++ w.drop (a + L) = w.drop a := by
      rw [seg, show a + L - a = L by omega, ← List.drop_drop, List.take_append_drop]
    rw [this, List.take_append_drop]
  have hta : (w.take a).length = a := by simp; omega
  have hsl : (seg w a (a + L)).length = L := by rw [length_seg w haL]; omega
  have hunion : ∀ P1 ∈ S1, ∀ P2 ∈ S2, (P1 ∪ P2).filter (· < a) = P1 ∧ (P1 ∪ P2).filter (a + L ≤ ·) = P2 := by
    intro P1 h1 P2 h2
    constructor
    · ext x; simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hx | hx, hxa⟩
        · exact hx
        · have := Finset.mem_Ico.1 (hS2 P2 h2 hx); omega
      · intro hx; exact ⟨Or.inl hx, Finset.mem_range.1 (hS1 P1 h1 hx)⟩
    · ext x; simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hx | hx, hxa⟩
        · have := Finset.mem_range.1 (hS1 P1 h1 hx); omega
        · exact hx
      · intro hx; exact ⟨Or.inr hx, (Finset.mem_Ico.1 (hS2 P2 h2 hx)).1⟩
  refine Finset.sum_nbij' (fun P => (P.filter (· < a), P.filter (a + L ≤ ·))) (fun PP => PP.1 ∪ PP.2)
    ?_ ?_ ?_ ?_ ?_
  · intro P hP
    obtain ⟨_, _, h1, h2⟩ := (hS P).1 hP
    exact Finset.mem_product.2 ⟨h1, h2⟩
  · intro PP hPP
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hPP
    obtain ⟨hf1, hf2⟩ := hunion PP.1 h1 PP.2 h2
    refine (hS _).2 ⟨Finset.union_subset ((hS1 _ h1).trans (Finset.range_subset_range.2 (by omega)))
      (fun x hx => Finset.mem_range.2 (Finset.mem_Ico.1 (hS2 _ h2 hx)).2), fun p hp hpa => ?_, ?_, ?_⟩
    · rcases Finset.mem_union.1 hp with hx | hx
      · have := Finset.mem_range.1 (hS1 _ h1 hx); omega
      · have := Finset.mem_Ico.1 (hS2 _ h2 hx); omega
    · rw [hf1]; exact h1
    · rw [hf2]; exact h2
  · intro P hP
    obtain ⟨_, hno, _, _⟩ := (hS P).1 hP
    ext x; simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hx
      by_cases hxa : x < a
      · exact Or.inl ⟨hx, hxa⟩
      · exact Or.inr ⟨hx, by have := hno x hx; omega⟩
  · intro PP hPP
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hPP
    obtain ⟨hf1, hf2⟩ := hunion PP.1 h1 PP.2 h2
    rw [hf1, hf2]
  · intro P hP
    obtain ⟨_, hno, _, _⟩ := (hS P).1 hP
    conv_lhs => rw [hw]
    rw [mixAux_append, mixAux_append, zero_add, hta, hsl, ← mul_assoc]
    congr 1
    · congr 1
      · refine mixAux_congr _ _ _ 0 fun x _ hx => ?_
        rw [hta] at hx
        simp only [Finset.mem_filter]
        exact ⟨fun h => ⟨h, by omega⟩, fun h => h.1⟩
      · exact mixAux_of_disjoint _ _ _ a fun p hp hpa => hno p hp (by rw [hsl] at hpa; exact hpa)
    · refine mixAux_congr _ _ _ (a + L) fun x hx _ => ?_
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨h, hx⟩, fun h => h.1⟩

theorem unbroken_filter_lt {P : Finset ℕ} {c₀ L c' a : ℕ} (h : c₀ + (c' + 1) * L ≤ a) :
    Unbroken (P.filter (· < a)) c₀ L c' ↔ Unbroken P c₀ L c' := by
  unfold Unbroken
  simp only [Finset.mem_filter]
  constructor
  · intro hu p hp hpc; exact hu p ⟨hp, by omega⟩ hpc
  · intro hu p hp hpc; exact hu p hp.1 hpc

theorem unbroken_filter_ge {P : Finset ℕ} {c₀ L c' b : ℕ} (h : b ≤ c₀ + c' * L) :
    Unbroken (P.filter (b ≤ ·)) c₀ L c' ↔ Unbroken P c₀ L c' := by
  unfold Unbroken
  simp only [Finset.mem_filter]
  constructor
  · intro hu p hp hpc; exact hu p ⟨hp, by omega⟩ hpc
  · intro hu p hp hpc; exact hu p hp.1 hpc

/-- The copy `c` of `α (u♯)^R β` is `u♯`. -/
theorem copy_seg (α β u : List (Fin 2)) {R c : ℕ} (hc : c < R) :
    seg (α ++ (List.replicate R u).flatten ++ β) (α.length + c * u.length) (α.length + c * u.length + u.length) = u := by
  rw [block_split α β u hc, seg, show α.length + c * u.length + u.length - (α.length + c * u.length) = u.length by omega,
    ← length_block_pre α u c, List.append_assoc, List.drop_left, List.take_left]

theorem length_block (α β u : List (Fin 2)) (R : ℕ) :
    (α ++ (List.replicate R u).flatten ++ β).length = α.length + R * u.length + β.length := by
  simp [List.length_flatten, List.map_replicate, List.sum_replicate]; omega

end Block

section FirstLast

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (A : ValAuto Q)

/-- `P` has its first unbroken copy at `c`. -/
def IsFirst (P : Finset ℕ) (c₀ L c : ℕ) : Prop := Unbroken P c₀ L c ∧ ∀ c' < c, ¬ Unbroken P c₀ L c'

/-- `P` has its last unbroken copy at `c` (among `R` copies). -/
def IsLast (P : Finset ℕ) (c₀ L R c : ℕ) : Prop := Unbroken P c₀ L c ∧ ∀ c', c < c' → c' < R → ¬ Unbroken P c₀ L c'

open Classical in
/-- Splitting: if each `P` is selected by at most one `c` and the term of every `P` selected by no `c` vanishes, the sum is the sum of the sums over each `c`. -/
theorem sum_partition {M : Type*} [AddCommMonoid M] (S : Finset (Finset ℕ)) (R : ℕ) (sel : Finset ℕ → ℕ → Prop)
    (f : Finset ℕ → M) (huniq : ∀ P c c', c < R → c' < R → sel P c → sel P c' → c = c')
    (hzero : ∀ P ∈ S, (∀ c < R, ¬ sel P c) → f P = 0) :
    ∑ P ∈ S, f P = ∑ c ∈ Finset.range R, ∑ P ∈ S.filter (fun P => sel P c), f P := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun P hP => ?_
  by_cases hex : ∃ c < R, sel P c
  · obtain ⟨c, hcR, hc⟩ := hex
    rw [Finset.sum_eq_single c]
    · simp [hc]
    · intro c' hc' hne
      have := Finset.mem_range.1 hc'
      simp only [ite_eq_right_iff]
      intro h; exact absurd (huniq P c' c this hcR h hc) hne
    · intro h; exact absurd (Finset.mem_range.2 hcR) h
  · push Not at hex
    rw [hzero P hP hex]
    simp

variable (h01 : ∀ C, IsComp A C → ZeroOne A C) {K : Set (BRel (ZIdx A))} {u : List (Fin 2)} {e : BRel (ZIdx A)}
  (hS : Sharp A K u e)
include hS

/-- If `P` has no unbroken copy (all `R` copies are broken), the term vanishes (`|P| ≥ R ≥ |Q|`). -/
theorem mix_zero_of_all_broken {w : List (Fin 2)} {R : ℕ} (hR : Fintype.card Q ≤ R) (c₀ : ℕ) {P : Finset ℕ}
    (hP : P ⊆ Finset.range w.length) (hall : ∀ c < R, ¬ Unbroken P c₀ u.length c) :
    mixAux (Dp A) (Ep A) P 0 w = 0 := by
  have hL : 1 ≤ u.length := List.length_pos_iff.2 hS.ne_nil
  have hcard : R ≤ P.card := by
    by_contra h
    obtain ⟨c, hc, hu⟩ := exists_unbroken P c₀ u.length R hL (by omega)
    exact hall c hc hu
  refine mixAux_eq_zero A ?_
  have : cntIn P 0 w.length = P.card := by
    unfold cntIn; congr 1
    rw [Finset.filter_true_of_mem]
    intro x hx; have := Finset.mem_range.1 (hP hx); omega
  omega

open Classical in
/-- **Cutting at the top part**: `B_w = Σ_{c < R} U_c D_{u♯} B_{w_{>a_c+|u♯|}}` (`w = α (u♯)^R β`, `a_c = |α| + c|u♯|`). -/
theorem block_first (hR : Fintype.card Q ≤ R) (α β : List (Fin 2)) :
    Rigid.DxN A.B (α ++ (List.replicate R u).flatten ++ β) =
      ∑ c ∈ Finset.range R,
        (∑ P1 ∈ (Finset.range (α.length + c * u.length)).powerset.filter
            (fun P => ∀ c' < c, ¬ Unbroken P α.length u.length c'),
          mixAux (Dp A) (Ep A) P1 0 ((α ++ (List.replicate R u).flatten ++ β).take (α.length + c * u.length))) *
          Rigid.DxN (Dp A) u *
          Rigid.DxN A.B ((α ++ (List.replicate R u).flatten ++ β).drop (α.length + c * u.length + u.length)) := by
  set w := α ++ (List.replicate R u).flatten ++ β
  have hlen := length_block α β u R
  have hall := DxN_add_eq_sum (Dp A) (Ep A) w 0
  rw [← B_eq_Dp_add_Ep A, zero_add, ← Finset.range_eq_Ico] at hall
  rw [hall]
  rw [sum_partition _ R (fun P c => IsFirst P α.length u.length c) _
    (fun P c c' hc hc' h h' => by
      rcases lt_trichotomy c c' with hlt | heq | hgt
      · exact absurd h.1 (h'.2 c hlt)
      · exact heq
      · exact absurd h'.1 (h.2 c' hgt))
    (fun P hP hn => mix_zero_of_all_broken A hS hR α.length (Finset.mem_powerset.1 hP) (fun c hc hu => by
      -- the smallest unbroken copy is selected
      have hex : ∃ c, c < R ∧ Unbroken P α.length u.length c := ⟨c, hc, hu⟩
      let c0 := Nat.find hex
      have hc0 := Nat.find_spec hex
      exact hn c0 hc0.1 ⟨hc0.2, fun c' hc' hu' => Nat.find_min hex hc' ⟨by omega, hu'⟩⟩))]
  refine Finset.sum_congr rfl fun c hc => ?_
  have hcR := Finset.mem_range.1 hc
  set a := α.length + c * u.length
  have haL : a + u.length ≤ w.length := by
    rw [hlen]; have : (c + 1) * u.length ≤ R * u.length := Nat.mul_le_mul_right _ (by omega)
    simp only [a]; nlinarith
  have hcL : α.length + (c + 1) * u.length = a + u.length := by simp only [a]; ring
  have hmem : ∀ P, P ∈ (Finset.range w.length).powerset.filter (fun P => IsFirst P α.length u.length c) ↔
      P ⊆ Finset.range w.length ∧ (∀ p ∈ P, ¬ (a ≤ p ∧ p < a + u.length)) ∧
        P.filter (· < a) ∈ (Finset.range a).powerset.filter (fun P => ∀ c' < c, ¬ Unbroken P α.length u.length c') ∧
        P.filter (a + u.length ≤ ·) ∈ (Finset.Ico (a + u.length) w.length).powerset := by
    intro P
    simp only [Finset.mem_filter, Finset.mem_powerset]
    unfold IsFirst
    have hsub1 : P.filter (· < a) ⊆ Finset.range a := fun x hx => Finset.mem_range.2 (Finset.mem_filter.1 hx).2
    have hfirst : (∀ c' < c, ¬ Unbroken (P.filter (· < a)) α.length u.length c') ↔
        (∀ c' < c, ¬ Unbroken P α.length u.length c') := by
      refine forall_congr' fun c' => imp_congr_right fun hc' => not_congr (unbroken_filter_lt ?_)
      have : (c' + 1) * u.length ≤ c * u.length := Nat.mul_le_mul_right _ (by omega)
      simp only [a]; omega
    rw [hfirst]
    constructor
    · rintro ⟨hP, hu, hf⟩
      refine ⟨hP, fun p hp hpa => hu p hp (by rw [hcL]; exact hpa), ⟨hsub1, hf⟩, fun x hx => ?_⟩
      rw [Finset.mem_filter] at hx
      exact Finset.mem_Ico.2 ⟨hx.2, Finset.mem_range.1 (hP hx.1)⟩
    · rintro ⟨hP, hno, ⟨_, hf⟩, _⟩
      exact ⟨hP, fun p hp hpc => hno p hp (by rw [hcL] at hpc; exact hpc), hf⟩
  rw [mix_block A w haL _ _ _ (fun P hP => Finset.mem_powerset.1 (Finset.mem_filter.1 hP).1)
    (fun P hP => Finset.mem_powerset.1 hP) hmem, copy_seg α β u hcR]
  congr 1
  have hd := DxN_add_eq_sum (Dp A) (Ep A) (w.drop (a + u.length)) (a + u.length)
  rw [← B_eq_Dp_add_Ep A] at hd
  rw [hd, List.length_drop, show a + u.length + (w.length - (a + u.length)) = w.length by omega]

open Classical in
/-- **Cutting at the low part**: `B_w = Σ_{c < R} B_{w_{≤a_c}} D_{u♯} W_c` (`W_c` is the sum for the part after in which every copy `c' > c` is broken). -/
theorem block_last (hR : Fintype.card Q ≤ R) (α β : List (Fin 2)) :
    Rigid.DxN A.B (α ++ (List.replicate R u).flatten ++ β) =
      ∑ c ∈ Finset.range R,
        Rigid.DxN A.B ((α ++ (List.replicate R u).flatten ++ β).take (α.length + c * u.length)) *
          Rigid.DxN (Dp A) u *
          (∑ P2 ∈ (Finset.Ico (α.length + c * u.length + u.length)
              (α ++ (List.replicate R u).flatten ++ β).length).powerset.filter
              (fun P => ∀ c', c < c' → c' < R → ¬ Unbroken P α.length u.length c'),
            mixAux (Dp A) (Ep A) P2 (α.length + c * u.length + u.length)
              ((α ++ (List.replicate R u).flatten ++ β).drop (α.length + c * u.length + u.length))) := by
  set w := α ++ (List.replicate R u).flatten ++ β
  have hlen := length_block α β u R
  have hall := DxN_add_eq_sum (Dp A) (Ep A) w 0
  rw [← B_eq_Dp_add_Ep A, zero_add, ← Finset.range_eq_Ico] at hall
  rw [hall]
  rw [sum_partition _ R (fun P c => IsLast P α.length u.length R c) _
    (fun P c c' hc hc' h h' => by
      rcases lt_trichotomy c c' with hlt | heq | hgt
      · exact absurd h'.1 (h.2 c' hlt hc')
      · exact heq
      · exact absurd h.1 (h'.2 c hgt hc))
    (fun P hP hn => mix_zero_of_all_broken A hS hR α.length (Finset.mem_powerset.1 hP) (fun c hc hu => by
      have hex : ∃ c, c < R ∧ Unbroken P α.length u.length c := ⟨c, hc, hu⟩
      classical
      let S := (Finset.range R).filter (fun c => Unbroken P α.length u.length c)
      have hne : S.Nonempty := ⟨c, by simp [S, hc, hu]⟩
      have hm := Finset.mem_filter.1 (Finset.max'_mem S hne)
      exact hn (S.max' hne) (Finset.mem_range.1 hm.1) ⟨hm.2, fun c' hc' hc'R hu' => by
        have := Finset.le_max' S c' (by simp [S, hc'R, hu']); omega⟩))]
  refine Finset.sum_congr rfl fun c hc => ?_
  have hcR := Finset.mem_range.1 hc
  set a := α.length + c * u.length
  have haL : a + u.length ≤ w.length := by
    rw [hlen]; have : (c + 1) * u.length ≤ R * u.length := Nat.mul_le_mul_right _ (by omega)
    simp only [a]; nlinarith
  have hcL : α.length + (c + 1) * u.length = a + u.length := by simp only [a]; ring
  have hmem : ∀ P, P ∈ (Finset.range w.length).powerset.filter (fun P => IsLast P α.length u.length R c) ↔
      P ⊆ Finset.range w.length ∧ (∀ p ∈ P, ¬ (a ≤ p ∧ p < a + u.length)) ∧
        P.filter (· < a) ∈ (Finset.range a).powerset ∧
        P.filter (a + u.length ≤ ·) ∈ (Finset.Ico (a + u.length) w.length).powerset.filter
          (fun P => ∀ c', c < c' → c' < R → ¬ Unbroken P α.length u.length c') := by
    intro P
    simp only [Finset.mem_filter, Finset.mem_powerset]
    unfold IsLast
    have hsub1 : P.filter (· < a) ⊆ Finset.range a := fun x hx => Finset.mem_range.2 (Finset.mem_filter.1 hx).2
    have hlast : (∀ c', c < c' → c' < R → ¬ Unbroken (P.filter (a + u.length ≤ ·)) α.length u.length c') ↔
        (∀ c', c < c' → c' < R → ¬ Unbroken P α.length u.length c') := by
      refine forall_congr' fun c' => imp_congr_right fun hc' => imp_congr_right fun _ =>
        not_congr (unbroken_filter_ge ?_)
      have : (c + 1) * u.length ≤ c' * u.length := Nat.mul_le_mul_right _ (by omega)
      omega
    rw [hlast]
    constructor
    · rintro ⟨hP, hu, hf⟩
      refine ⟨hP, fun p hp hpa => hu p hp (by rw [hcL]; exact hpa), hsub1, fun x hx => ?_, hf⟩
      rw [Finset.mem_filter] at hx
      exact Finset.mem_Ico.2 ⟨hx.2, Finset.mem_range.1 (hP hx.1)⟩
    · rintro ⟨hP, hno, _, _, hf⟩
      exact ⟨hP, fun p hp hpc => hno p hp (by rw [hcL] at hpc; exact hpc), hf⟩
  rw [mix_block A w haL _ _ _ (fun P hP => Finset.mem_powerset.1 hP)
    (fun P hP => Finset.mem_powerset.1 (Finset.mem_filter.1 hP).1) hmem, copy_seg α β u hcR]
  congr 2
  have hd := DxN_add_eq_sum (Dp A) (Ep A) (w.take a) 0
  rw [← B_eq_Dp_add_Ep A, zero_add, ← Finset.range_eq_Ico, List.length_take,
    show min a w.length = a by omega] at hd
  rw [hd]

end FirstLast

end Collatz.Arctic.NatQ5.W3c
