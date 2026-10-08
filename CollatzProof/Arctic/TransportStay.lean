/-
Lemma 6.3 (i)–(iii) along sequences and words, Lemma 6.3 (iv) (the stay lemma), and the summary. Definitions and §1–§3 are in `Transport.lean`.
-/
import CollatzProof.Arctic.Transport

namespace Collatz.Arctic.MinIdeal

open BRel

/-! ## 4. Iteration: transport along a sequence of occurrences -/

section Iter

variable {Q : Type*} {E : BRel Q}

/-- The composition `π_{Xₙ} ∘ ⋯ ∘ π_{X₁}` of the permutations of a sequence `X₁, …, Xₙ` of types of the words between occurrences. -/
noncomputable def piList (hE : E * E = E) : List (BRel Q) → (Cls E hE ≃o Cls E hE)
  | [] => OrderIso.refl _
  | X :: Xs => (piX hE X).trans (piList hE Xs)

/-- The type `X₁E X₂E ⋯ XₙE` from the end of an occurrence to the end of a later occurrence. -/
def segProd (E : BRel Q) (Xs : List (BRel Q)) : BRel Q := (Xs.map (· * E)).prod

theorem segProd_cons (X : BRel Q) (Xs : List (BRel Q)) :
    segProd E (X :: Xs) = X * E * segProd E Xs := by
  simp [segProd]

/-- **Lemma 6.3 (iii)**: an index alive at time `θ_{n'}` that comes from an index in `β_j` at time `θ_n` lies in
`β_{π_{n'-1} ⋯ π_n (j)}`. -/
theorem carry_list (hE : E * E = E) :
    ∀ (Xs : List (BRel Q)), (∀ X ∈ Xs, InH E (E * X * E)) →
      ∀ {j : Cls E hE} {k b : Q}, beta hE j k → segProd E Xs k b → beta hE (piList hE Xs j) b
  | [], _, j, k, b, hk, hkb => by
    simp only [segProd, List.map_nil, List.prod_nil, one_apply] at hkb
    subst hkb; exact hk
  | X :: Xs, hXs, j, k, b, hk, hkb => by
    rw [segProd_cons, mul_apply] at hkb
    obtain ⟨m, hkm, hmb⟩ := hkb
    have h1 := carry_one hE (hXs X (List.mem_cons_self ..)) hk hkm
    exact carry_list hE Xs (fun Y hY => hXs Y (List.mem_cons_of_mem _ hY)) h1 hmb

/-- **Lemma 6.3 (i) (sequence)**: `(⋃_{i∈I} β_i)·X₁E⋯XₙE = ⋃_{i∈I} β_{π(i)}` with `π := π_{Xₙ} ∘ ⋯ ∘ π_{X₁}`. -/
theorem act_betaUnion_list (hE : E * E = E) :
    ∀ (Xs : List (BRel Q)), (∀ X ∈ Xs, InH E (E * X * E)) → ∀ (I : Set (Cls E hE)),
      act (betaUnion hE I) (segProd E Xs) = betaUnion hE (piList hE Xs '' I)
  | [], _, I => by
    simp only [segProd, List.map_nil, List.prod_nil, act_one, piList]
    simp
  | X :: Xs, hXs, I => by
    rw [segProd_cons, ← act_mul, ← act_mul,
      act_betaUnion hE (hXs X (List.mem_cons_self ..)) I,
      act_betaUnion_list hE Xs (fun Y hY => hXs Y (List.mem_cons_of_mem _ hY))]
    congr 1
    simp only [piList, OrderIso.coe_trans, Set.image_comp]

/-- Components are preserved under the permutation of a sequence: `C(π(j)) = C(j)`. -/
theorem comp_piList [Finite Q] {B₀ B₁ : BRel Q} (hE : E * E = E) (hEM : E ∈ Mon B₀ B₁) :
    ∀ (Xs : List (BRel Q)), (∀ X ∈ Xs, X ∈ Mon B₀ B₁ ∧ InH E (E * X * E)) → ∀ j : Cls E hE,
      comp B₀ B₁ hE (piList hE Xs j) = comp B₀ B₁ hE j
  | [], _, j => rfl
  | X :: Xs, hXs, j => by
    have hX := hXs X (List.mem_cons_self ..)
    change comp B₀ B₁ hE (piList hE Xs (piX hE X j)) = _
    rw [comp_piList hE hEM Xs (fun Y hY => hXs Y (List.mem_cons_of_mem _ hY)),
      comp_piX hE hEM hX.1 hX.2]

end Iter

/-! ## 5. Lemma 6.3 (iv): the stay lemma -/

section Stay

variable {Q : Type*} {B₀ B₁ E : BRel Q}

/-- **Lemma 6.3 (iv) (stay), first half**: if `a, b` lie in the same component and `E a b` (from `a` to `b` over a whole occurrence of `u*`),
then some index `c` of `C_E` lies in the same component with `E a c` and `E c b`. The component equals the component `C([c])` of the class of `c`. -/
theorem stay [Finite Q] (hE : E * E = E) (hEM : E ∈ Mon B₀ B₁) {a b : Q}
    (hba : Reach B₀ B₁ b a) (hab : E a b) :
    ∃ c, ∃ hc : E c c, E a c ∧ E c b ∧ Reach B₀ B₁ a c ∧ Reach B₀ B₁ c a ∧
      a ∈ comp B₀ B₁ hE (cls hE c hc) ∧ b ∈ comp B₀ B₁ hE (cls hE c hc) := by
  obtain ⟨c, hc, hac, hcb⟩ := factor hE hab
  have rac := reach_of_mem hEM a c hac
  have rcb := reach_of_mem hEM c b hcb
  have rca := rcb.trans hba
  refine ⟨c, hc, hac, hcb, rac, rca, ⟨c, hc, rfl, rac, rca⟩, ⟨c, hc, rfl, hba.trans rac, rcb⟩⟩

/-- **Lemma 6.3 (iv) (stay)**: if moreover the support `S` contains `a` and `S·E = ⋃_{i∈I} β_i` (`I` an upper set), then
the class `j` of `c` lies in `I` (an occupied class) and `b ∈ β_j`. -/
theorem stay_supp [Finite Q] (hE : E * E = E) (hEM : E ∈ Mon B₀ B₁) {a b : Q}
    (hba : Reach B₀ B₁ b a) (hab : E a b) {S : Set Q} {I : Set (Cls E hE)} (hI : IsUpperSet I)
    (hS : act S E = betaUnion hE I) (ha : a ∈ S) :
    ∃ c, ∃ hc : E c c, E a c ∧ E c b ∧ Reach B₀ B₁ a c ∧ Reach B₀ B₁ c a ∧
      a ∈ comp B₀ B₁ hE (cls hE c hc) ∧ b ∈ comp B₀ B₁ hE (cls hE c hc) ∧
      cls hE c hc ∈ I ∧ beta hE (cls hE c hc) b := by
  obtain ⟨c, hc, hac, hcb, rac, rca, hca, hcb'⟩ := stay hE hEM hba hab
  have hcS : c ∈ betaUnion hE I := hS ▸ (⟨a, ha, hac⟩ : c ∈ act S E)
  exact ⟨c, hc, hac, hcb, rac, rca, hca, hcb', (mem_betaUnion_of_C hE hI hc).1 hcS, hcb⟩

end Stay

/-! ## 6. The word layer: sequences of letters and the forward support process -/

section Words

variable {Q : Type*} {B₀ B₁ E : BRel Q}

/-- The type of a letter (`false ↦ B₀`, `true ↦ B₁`). -/
def letter (B₀ B₁ : BRel Q) (b : Bool) : BRel Q := if b then B₁ else B₀

/-- The type of a word (the product of the types of its letters). The forward support process is `S ↦ S·typ w`. -/
def typ (B₀ B₁ : BRel Q) (w : List Bool) : BRel Q := (w.map (letter B₀ B₁)).prod

theorem typ_nil : typ B₀ B₁ [] = 1 := rfl

theorem typ_append (w w' : List Bool) : typ B₀ B₁ (w ++ w') = typ B₀ B₁ w * typ B₀ B₁ w' := by
  simp [typ, List.map_append, List.prod_append]

theorem letter_mem (b : Bool) : letter B₀ B₁ b ∈ Mon B₀ B₁ := by
  cases b
  · exact Submonoid.subset_closure (by simp [letter])
  · exact Submonoid.subset_closure (by simp [letter])

/-- The type of a word lies in `M`. -/
theorem typ_mem : ∀ w : List Bool, typ B₀ B₁ w ∈ Mon B₀ B₁
  | [] => Submonoid.one_mem _
  | b :: w => by
    have : typ B₀ B₁ (b :: w) = letter B₀ B₁ b * typ B₀ B₁ w := by simp [typ]
    rw [this]; exact Submonoid.mul_mem _ (letter_mem b) (typ_mem w)

/-- The word `x₁ u x₂ u ⋯ xₙ u`, in which every word between occurrences is followed by an occurrence, has type `X₁E⋯XₙE` (`u` has type `E`, `Xᵢ := typ xᵢ`). -/
theorem typ_segs (u : List Bool) (hu : typ B₀ B₁ u = E) :
    ∀ xs : List (List Bool),
      typ B₀ B₁ (xs.map (· ++ u)).flatten = segProd E (xs.map (typ B₀ B₁))
  | [] => rfl
  | x :: xs => by
    rw [List.map_cons, List.flatten_cons, typ_append, typ_append, hu, typ_segs u hu xs,
      List.map_cons, segProd_cons]

/-- **Lemma 6.3 (i) (word form)**: reading an arbitrary word `w₀ u x₁ u ⋯ xₙ u` (`u` is the word `u*` of type `E`) from the support `S`
gives the support `⋃_{i∈π(I₁)} β_i`, where `I₁` is the upper set at the end of the first occurrence (the classes hit by `S·typ w₀`) and
`π := π_{typ xₙ} ∘ ⋯ ∘ π_{typ x₁}`. -/
theorem act_word [Finite Q] {K : Set (BRel Q)} (hK : IsMinIdeal (Mon B₀ B₁) K) (hEK : E ∈ K)
    (hE : E * E = E) (u : List Bool) (hu : typ B₀ B₁ u = E) (S : Set Q) (w₀ : List Bool)
    (xs : List (List Bool)) :
    act S (typ B₀ B₁ (w₀ ++ u ++ (xs.map (· ++ u)).flatten)) =
      betaUnion hE (piList hE (xs.map (typ B₀ B₁)) '' hitSet hE (act S (typ B₀ B₁ w₀))) := by
  have hgrp : ∀ X ∈ xs.map (typ B₀ B₁), InH E (E * X * E) := by
    intro X hX
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hX
    exact inH_of_minIdeal hK hEK hE (typ_mem x)
  rw [typ_append, typ_append, hu, typ_segs u hu xs, ← act_mul, ← act_mul,
    act_E_eq_betaUnion hE, act_betaUnion_list hE _ hgrp]

end Words

/-! ## 7. Summary: Lemma 6.3 -/

section Summary

variable {Q : Type*}

/-- **Lemma 6.3 (i)–(iii) (transport)**. For an idempotent `E` of the minimal ideal `K` of the monoid `M` of `B₀, B₁` on a finite `Q` and
`X ∈ M`, let `π := π_X` (the permutation of `R := E X E ∈ 𝒢_E`, `perm_of_inH`). Then:
* (Lemma 6.2 (iii)) `(E X E)_q = β_{π [q]}` (`π` is unique with this property).
* (i) For every set of classes `I`, `(⋃_{i∈I} β_i)·X·E = ⋃_{i∈I} β_{π(i)}`. If `I` is an upper set, so is `π(I)`.
* (ii) `C(π(j)) = C(j)`.
* (iii) If `k ∈ β_j`, then `k·(X E) ⊆ β_{π(j)}`. -/
theorem lemma_56_10_1 [Finite Q] (B₀ B₁ : BRel Q) {K : Set (BRel Q)}
    (hK : IsMinIdeal (Mon B₀ B₁) K) {E : BRel Q} (hEK : E ∈ K) (hE : E * E = E)
    {X : BRel Q} (hXM : X ∈ Mon B₀ B₁) :
    (∀ q (hq : E q q), (E * X * E) q = beta hE (piX hE X (cls hE q hq))) ∧
    (∀ I : Set (Cls E hE), act (act (betaUnion hE I) X) E = betaUnion hE (piX hE X '' I)) ∧
    (∀ I : Set (Cls E hE), IsUpperSet I → IsUpperSet (piX hE X '' I)) ∧
    (∀ j : Cls E hE, comp B₀ B₁ hE (piX hE X j) = comp B₀ B₁ hE j) ∧
    (∀ (j : Cls E hE) (k b : Q), beta hE j k → (X * E) k b → beta hE (piX hE X j) b) := by
  have hEM : E ∈ Mon B₀ B₁ := hK.1.2.1 hEK
  have hX : InH E (E * X * E) := inH_of_minIdeal hK hEK hE hXM
  exact ⟨piX_spec hE hX, act_betaUnion hE hX, fun I hI => piX_isUpperSet hE X hI,
    comp_piX hE hEM hXM hX, fun j k b hk hb => carry_one hE hX hk hb⟩

/-- **Lemma 6.3 (i)–(iii), sequence form**. For a sequence `X₁, …, Xₙ ∈ M` of types (the types of the words between disjoint occurrences of `u*`),
let `π := π_{Xₙ} ∘ ⋯ ∘ π_{X₁}`. Then the support at the end of an occurrence `S·E = ⋃_{i∈I} β_i` (`I` the classes hit by `S`, an upper set) is
transported to `S·E·X₁E⋯XₙE = ⋃_{i∈I} β_{π(i)}`, `π(I)` is an upper set, `C(π(j)) = C(j)`, and
the indices alive that come from `β_j` lie in `β_{π(j)}`. -/
theorem lemma_56_10_1_list [Finite Q] (B₀ B₁ : BRel Q) {K : Set (BRel Q)}
    (hK : IsMinIdeal (Mon B₀ B₁) K) {E : BRel Q} (hEK : E ∈ K) (hE : E * E = E)
    (Xs : List (BRel Q)) (hXs : ∀ X ∈ Xs, X ∈ Mon B₀ B₁) (S : Set Q) :
    act S E = betaUnion hE (hitSet hE S) ∧ IsUpperSet (hitSet hE S) ∧
    act (act S E) (segProd E Xs) = betaUnion hE (piList hE Xs '' hitSet hE S) ∧
    IsUpperSet (piList hE Xs '' hitSet hE S) ∧
    (∀ j : Cls E hE, comp B₀ B₁ hE (piList hE Xs j) = comp B₀ B₁ hE j) ∧
    (∀ (j : Cls E hE) (k b : Q), beta hE j k → segProd E Xs k b → beta hE (piList hE Xs j) b) := by
  have hEM : E ∈ Mon B₀ B₁ := hK.1.2.1 hEK
  have hgrp : ∀ X ∈ Xs, InH E (E * X * E) := fun X hX => inH_of_minIdeal hK hEK hE (hXs X hX)
  refine ⟨act_E_eq_betaUnion hE S, hitSet_isUpperSet hE S, ?_,
    (hitSet_isUpperSet hE S).image _, comp_piList hE hEM Xs (fun X hX => ⟨hXs X hX, hgrp X hX⟩),
    fun j k b hk hb => carry_list hE Xs hgrp hk hb⟩
  rw [act_E_eq_betaUnion hE S, act_betaUnion_list hE Xs hgrp]

/-- **Lemma 6.3 (iv) (stay)**, in the form with the hypothesis of a minimal ideal. -/
theorem corollary_56_10_2 [Finite Q] (B₀ B₁ : BRel Q) {K : Set (BRel Q)}
    (hK : IsMinIdeal (Mon B₀ B₁) K) {E : BRel Q} (hEK : E ∈ K) (hE : E * E = E) {a b : Q}
    (hab' : Reach B₀ B₁ a b ∧ Reach B₀ B₁ b a) (hab : E a b) {S : Set Q} (ha : a ∈ S) :
    ∃ c, ∃ hc : E c c, E a c ∧ E c b ∧
      a ∈ comp B₀ B₁ hE (cls hE c hc) ∧ b ∈ comp B₀ B₁ hE (cls hE c hc) ∧
      cls hE c hc ∈ hitSet hE S ∧ beta hE (cls hE c hc) b := by
  have hEM : E ∈ Mon B₀ B₁ := hK.1.2.1 hEK
  obtain ⟨c, hc, hac, hcb, -, -, hca, hcb', hI, hb⟩ :=
    stay_supp hE hEM hab'.2 hab (hitSet_isUpperSet hE S) (act_E_eq_betaUnion hE S) ha
  exact ⟨c, hc, hac, hcb, hca, hcb', hI, hb⟩

end Summary

/-! ## 8. Sanity check: components are not trivial -/

section Example

/-- Reachability in the graph of `leRel` (`≤` on `Fin 2`) preserves `≤`. -/
theorem reach_leRel_le {a b : Fin 2} (h : Reach leRel leRel a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ hyz ih => rcases hyz with h | h <;> exact le_trans ih h

/-- For `B₀ = B₁ = ≤` (`Fin 2`) the components of the classes `[0]` and `[1]` differ (`C([0]) ∌ 1`).
This confirms that the definition of `comp` does not collapse to the whole set. -/
theorem leRel_comp_ne :
    comp leRel leRel leRel_idem (cls leRel_idem 0 (le_refl _)) ≠
      comp leRel leRel leRel_idem (cls leRel_idem 1 (le_refl _)) := by
  intro h
  have h1 : (1 : Fin 2) ∈ comp leRel leRel leRel_idem (cls leRel_idem 1 (le_refl _)) :=
    ⟨1, le_refl _, rfl, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  rw [← h] at h1
  obtain ⟨q, hq, heq, h1q, hq1⟩ := h1
  have hq0 : q = 0 := by
    have := ((cls_eq_cls leRel_idem hq (le_refl (0 : Fin 2))).1 heq).1
    exact le_antisymm this (Fin.zero_le _)
  subst hq0
  exact absurd (reach_leRel_le h1q) (by decide)

end Example

end Collatz.Arctic.MinIdeal

#print axioms Collatz.Arctic.MinIdeal.lemma_56_10_1
#print axioms Collatz.Arctic.MinIdeal.lemma_56_10_1_list
#print axioms Collatz.Arctic.MinIdeal.corollary_56_10_2
#print axioms Collatz.Arctic.MinIdeal.stay_supp
#print axioms Collatz.Arctic.MinIdeal.act_word
#print axioms Collatz.Arctic.MinIdeal.leRel_comp_ne
