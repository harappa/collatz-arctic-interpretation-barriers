/-
Check of the weakened-premise statements (`DPWeak.lean`, `DPWeak2.lean`): counterexamples for the premises that cannot be dropped
(Proposition 4.2). All interpretations have dimension 1.

* §1 Premises that cannot be dropped (counterexamples), written with the general forms `BarrierDPFor L U P`, `BarrierBZFor L U P` of `NonVacuity.lean` (`L` is the list of
  symbols on which the condition is imposed).
  - **The condition on the marked symbol cannot be dropped** (in all four statements): even if all unmarked symbols are somewhere finite (below zero:
    absolutely positive), interpreting `h#` as the constant −∞ and the unmarked symbols as `x ↦ x ⊕ 0` makes both sides of each rule of `U` equal,
    and both sides of each dependency pair the constant −∞, which is strictly oriented in the first row (`−∞ ≫ −∞` of Koprowski–Waldmann 2009). See `dw_not_DP_noMark` etc.
  - **Over `𝔸_ℕ`, somewhere finiteness of the end symbol cannot be dropped**: even if all symbols of `lettersPB` except `rgt` are somewhere finite,
    the interpretation with weight −∞ on `rgt`, 0 on `f`, `t`, `lft#` and 1 on the digits strictly orients all of `P_B` (`dw_not_DP_noRgt`).
    The same for the reversed problem (−∞ on `lft`, 1 on `f`, `t`, 0 on the others; `dw_not_DPrev_noLft`).
    Corollary: **the form imposing somewhere finiteness on the marked symbol only is false** (`dw_not_DP_markOnly`, `dw_not_DPrev_markOnly`).
    This contrasts with below zero, where the form imposing absolute positivity on the marked symbol only holds (`arcticBarrierBZw`).
    Over `𝔸_ℕ` too, if the first component of the absolute part of `h#` is finite, no condition on other symbols is needed (the left case of `SFRoot`).
* Non-vacuity (§2) and the form under the Collatz conjecture (§3, dropping also the conditions on `f`, `t`) are in `DPWeak4.lean`.
-/
import CollatzProof.Arctic.DPWeak2
import CollatzProof.Arctic.NonVacuity2

namespace Collatz.Arctic

open Matrix NonVacuity

/-! ## §1a The condition on the marked symbol cannot be dropped -/

lemma dw_evA_cons {R : Type} [CommSemiring R] {d : ℕ} (J : DLetter → AffFun R d) (s : DLetter)
    (L : List DLetter) : evA J (s :: L) = (J s).comp (evA J L) := rfl

/-- The interpretation with the marked symbols as the constant −∞ (`⟨0, 0⟩`) and the unmarked symbols as `x ↦ x ⊕ 0` (`⟨1, 1⟩`). -/
def dw_Jneg {R : Type} [CommSemiring R] {d : ℕ} : DLetter → AffFun R d
  | DLetter.mark _ => ⟨0, 0⟩
  | DLetter.plain _ => ⟨1, fun _ => 1⟩

lemma dw_evA_Jneg_head {R : Type} [CommSemiring R] {d : ℕ} (L : List DLetter) (h : Letter)
    (hL : L.head? = some (DLetter.mark h)) : evA (dw_Jneg (R := R) (d := d)) L = ⟨0, 0⟩ := by
  cases L with
  | nil => simp at hL
  | cons s L =>
    simp only [List.head?_cons, Option.some.injEq] at hL
    subst hL
    rw [dw_evA_cons]
    simp [dw_Jneg, AffFun.comp]

lemma dw_evA_Jneg_plain {R : Type} [CommSemiring R] {d : ℕ} (h11 : (1 : R) + 1 = 1) :
    ∀ L : List Letter, L ≠ [] →
      evA (dw_Jneg (R := R) (d := d)) (L.map DLetter.plain) = ⟨1, fun _ => 1⟩
  | [], hL => absurd rfl hL
  | [s], _ => by
    rw [List.map_singleton, dw_evA_cons]
    simp [dw_Jneg, AffFun.comp, evA, AffFun.id]
  | s :: s' :: L, _ => by
    rw [List.map_cons, dw_evA_cons, dw_evA_Jneg_plain h11 (s' :: L) (by simp)]
    simp only [dw_Jneg, AffFun.comp, Matrix.one_mul, Matrix.one_mulVec, AffFun.mk.injEq, true_and]
    funext i
    simp [h11]

lemma dw_arc_one_add : (1 : Arc) + 1 = 1 := by decide
lemma dw_arcZ_one_add : (1 : ArcZ) + 1 = 1 := by decide

theorem dw_usableST_ne : ∀ ρ ∈ usableST, ρ.lhs ≠ [] ∧ ρ.rhs ≠ [] := by decide
theorem dw_usableSTrev_ne : ∀ ρ ∈ usableSTrev, ρ.lhs ≠ [] ∧ ρ.rhs ≠ [] := by decide
theorem dw_pairsPB_head : ∀ π ∈ pairsPB,
    π.lhs.head? = some (DLetter.mark Letter.lft) ∧
      π.rhs.head? = some (DLetter.mark Letter.lft) := by
  decide
theorem dw_pairsPDrev_head : ∀ π ∈ pairsPDrev,
    π.lhs.head? = some (DLetter.mark Letter.rgt) ∧
      π.rhs.head? = some (DLetter.mark Letter.rgt) := by
  decide

/-- `𝔸_ℕ`, forward: false if there is no condition on `lft#`, even if all unmarked symbols are somewhere finite. -/
theorem dw_not_DP_noMark : ¬ BarrierDPFor lettersPB.tail usableST pairsPB := by
  intro h
  refine h 1 Nat.one_pos dw_Jneg ?_ ?_ ?_ _ (List.mem_cons_self ..) ?_
  · intro s hs
    cases s with
    | mark a => simp [lettersPB] at hs
    | plain a => exact Or.inl (fin_ne_zero 0)
  · intro ρ hρ
    show WeakA (evA _ (ρ.lhs.map _)) (evA _ (ρ.rhs.map _))
    rw [dw_evA_Jneg_plain dw_arc_one_add _ (dw_usableST_ne ρ hρ).1,
      dw_evA_Jneg_plain dw_arc_one_add _ (dw_usableST_ne ρ hρ).2]
    exact ⟨fun _ _ => le_rfl, fun _ => le_rfl⟩
  · intro π hπ
    rw [dw_evA_Jneg_head _ _ (dw_pairsPB_head π hπ).1,
      dw_evA_Jneg_head _ _ (dw_pairsPB_head π hπ).2]
    exact ⟨fun _ => le_rfl, le_rfl⟩
  · rw [dw_evA_Jneg_head _ _ (dw_pairsPB_head _ (List.mem_cons_self ..)).1,
      dw_evA_Jneg_head _ _ (dw_pairsPB_head _ (List.mem_cons_self ..)).2]
    exact ⟨fun _ => Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- `𝔸_ℕ`, reversed: the same. -/
theorem dw_not_DPrev_noMark : ¬ BarrierDPFor lettersPDrev.tail usableSTrev pairsPDrev := by
  intro h
  refine h 1 Nat.one_pos dw_Jneg ?_ ?_ ?_ _ (List.mem_cons_self ..) ?_
  · intro s hs
    cases s with
    | mark a => simp [lettersPDrev] at hs
    | plain a => exact Or.inl (fin_ne_zero 0)
  · intro ρ hρ
    show WeakA (evA _ (ρ.lhs.map _)) (evA _ (ρ.rhs.map _))
    rw [dw_evA_Jneg_plain dw_arc_one_add _ (dw_usableSTrev_ne ρ hρ).1,
      dw_evA_Jneg_plain dw_arc_one_add _ (dw_usableSTrev_ne ρ hρ).2]
    exact ⟨fun _ _ => le_rfl, fun _ => le_rfl⟩
  · intro π hπ
    rw [dw_evA_Jneg_head _ _ (dw_pairsPDrev_head π hπ).1,
      dw_evA_Jneg_head _ _ (dw_pairsPDrev_head π hπ).2]
    exact ⟨fun _ => le_rfl, le_rfl⟩
  · rw [dw_evA_Jneg_head _ _ (dw_pairsPDrev_head _ (List.mem_cons_self ..)).1,
      dw_evA_Jneg_head _ _ (dw_pairsPDrev_head _ (List.mem_cons_self ..)).2]
    exact ⟨fun _ => Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- Below zero, forward: false if there is no condition on `lft#`, even if all unmarked symbols are absolutely positive. -/
theorem dw_not_BZ_noMark : ¬ BarrierBZFor lettersPB.tail usableST pairsPB := by
  intro h
  refine h 1 Nat.one_pos dw_Jneg ?_ ?_ ?_ _ (List.mem_cons_self ..) ?_
  · intro s hs
    cases s with
    | mark a => simp [lettersPB] at hs
    | plain a => exact le_rfl
  · intro ρ hρ
    show WeakA (evA _ (ρ.lhs.map _)) (evA _ (ρ.rhs.map _))
    rw [dw_evA_Jneg_plain dw_arcZ_one_add _ (dw_usableST_ne ρ hρ).1,
      dw_evA_Jneg_plain dw_arcZ_one_add _ (dw_usableST_ne ρ hρ).2]
    exact ⟨fun _ _ => le_rfl, fun _ => le_rfl⟩
  · intro π hπ
    rw [dw_evA_Jneg_head _ _ (dw_pairsPB_head π hπ).1,
      dw_evA_Jneg_head _ _ (dw_pairsPB_head π hπ).2]
    exact ⟨fun _ => le_rfl, le_rfl⟩
  · rw [dw_evA_Jneg_head _ _ (dw_pairsPB_head _ (List.mem_cons_self ..)).1,
      dw_evA_Jneg_head _ _ (dw_pairsPB_head _ (List.mem_cons_self ..)).2]
    exact ⟨fun _ => Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- Below zero, reversed: the same. -/
theorem dw_not_BZrev_noMark : ¬ BarrierBZFor lettersPDrev.tail usableSTrev pairsPDrev := by
  intro h
  refine h 1 Nat.one_pos dw_Jneg ?_ ?_ ?_ _ (List.mem_cons_self ..) ?_
  · intro s hs
    cases s with
    | mark a => simp [lettersPDrev] at hs
    | plain a => exact le_rfl
  · intro ρ hρ
    show WeakA (evA _ (ρ.lhs.map _)) (evA _ (ρ.rhs.map _))
    rw [dw_evA_Jneg_plain dw_arcZ_one_add _ (dw_usableSTrev_ne ρ hρ).1,
      dw_evA_Jneg_plain dw_arcZ_one_add _ (dw_usableSTrev_ne ρ hρ).2]
    exact ⟨fun _ _ => le_rfl, fun _ => le_rfl⟩
  · intro π hπ
    rw [dw_evA_Jneg_head _ _ (dw_pairsPDrev_head π hπ).1,
      dw_evA_Jneg_head _ _ (dw_pairsPDrev_head π hπ).2]
    exact ⟨fun _ => le_rfl, le_rfl⟩
  · rw [dw_evA_Jneg_head _ _ (dw_pairsPDrev_head _ (List.mem_cons_self ..)).1,
      dw_evA_Jneg_head _ _ (dw_pairsPDrev_head _ (List.mem_cons_self ..)).2]
    exact ⟨fun _ => Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

/-! ## §1b Over `𝔸_ℕ`, somewhere finiteness of the end symbol cannot be dropped -/

/-- The interpretation of dimension 1 that sends a symbol `s` to `x ↦ w(s) ⊗ x` (`w(s) ∈ ℕ ∪ {−∞}`, absolute part −∞). -/
def dw_wJA (w : DLetter → Arc) : DLetter → AffFun Arc 1 := fun s => ⟨fun _ _ => w s, 0⟩

lemma dw_evA_wJA (w : DLetter → Arc) (x : List DLetter) :
    (∀ i j, (evA (dw_wJA w) x).M i j = (x.map w).prod) ∧ (evA (dw_wJA w) x).c = 0 := by
  induction x with
  | nil =>
    refine ⟨fun i j => ?_, rfl⟩
    have hij : i = j := Subsingleton.elim i j
    subst hij
    show (1 : AMat 1) i i = _
    simp only [Matrix.one_apply_eq, List.map_nil, List.prod_nil]
  | cons s x ih =>
    obtain ⟨ihM, ihc⟩ := ih
    refine ⟨fun i j => ?_, ?_⟩
    · show ((dw_wJA w s).M * (evA (dw_wJA w) x).M) i j = _
      rw [Matrix.mul_apply, Fin.sum_univ_one, ihM]
      simp only [dw_wJA, List.map_cons, List.prod_cons]
    · show (dw_wJA w s).M *ᵥ (evA (dw_wJA w) x).c + (dw_wJA w s).c = 0
      rw [ihc, Matrix.mulVec_zero, zero_add]
      rfl

lemma dw_weakA_wJA (w : DLetter → Arc) (u v : List DLetter) (h : (v.map w).prod ≤ (u.map w).prod) :
    WeakA (evA (dw_wJA w) u) (evA (dw_wJA w) v) := by
  unfold WeakA
  simp only [(dw_evA_wJA w u).1, (dw_evA_wJA w v).1, (dw_evA_wJA w u).2, (dw_evA_wJA w v).2]
  exact ⟨fun _ _ => h, fun _ => le_rfl⟩

lemma dw_weakTop_wJA (w : DLetter → Arc) (u v : List DLetter)
    (h : (v.map w).prod ≤ (u.map w).prod) :
    WeakTop Nat.one_pos (evA (dw_wJA w) u) (evA (dw_wJA w) v) := by
  unfold WeakTop
  simp only [(dw_evA_wJA w u).1, (dw_evA_wJA w v).1, (dw_evA_wJA w u).2, (dw_evA_wJA w v).2]
  exact ⟨fun _ => h, le_rfl⟩

lemma dw_strictTop_wJA (w : DLetter → Arc) (u v : List DLetter)
    (h : GG (u.map w).prod (v.map w).prod) :
    StrictTop Nat.one_pos (evA (dw_wJA w) u) (evA (dw_wJA w) v) := by
  unfold StrictTop
  simp only [(dw_evA_wJA w u).1, (dw_evA_wJA w v).1, (dw_evA_wJA w u).2, (dw_evA_wJA w v).2]
  exact ⟨fun _ => h, Or.inr ⟨rfl, rfl⟩⟩

open Letter DLetter in
/-- Weights for the forward counterexample: −∞ on `rgt`, 1 on the digits, 0 on the others (`lft#`, `f`, `t`). -/
def dw_wNoRgt : DLetter → Arc
  | plain rgt => 0
  | plain d0 => Arc.fin 1
  | plain d1 => Arc.fin 1
  | plain d2 => Arc.fin 1
  | _ => Arc.fin 0

open Letter DLetter in
/-- Weights for the reversed counterexample: −∞ on `lft`, 1 on `f`, `t`, 0 on the others (`rgt#`, the digits). -/
def dw_wNoLft : DLetter → Arc
  | plain lft => 0
  | plain f => Arc.fin 1
  | plain t => Arc.fin 1
  | _ => Arc.fin 0

/-- Monotonicity of the general form: the form with fewer constrained symbols implies the original form. -/
theorem dw_barrierDPFor_mono {L L' : List DLetter} {U : List Rule} {P : List DRule}
    (hLL : ∀ s ∈ L, s ∈ L') (h : BarrierDPFor L U P) : BarrierDPFor L' U P :=
  fun d hd J hSF => h d hd J (fun s hs => hSF s (hLL s hs))

/-- Forward (`𝔸_ℕ`): false even if all symbols except `rgt` are somewhere finite. -/
theorem dw_not_DP_noRgt :
    ¬ BarrierDPFor (lettersPB.erase (DLetter.plain Letter.rgt)) usableST pairsPB := by
  intro h
  have hSF : ∀ s ∈ lettersPB.erase (DLetter.plain Letter.rgt), dw_wNoRgt s ≠ 0 := by decide
  have hU : ∀ ρ ∈ usableST,
      (ρ.plain.rhs.map dw_wNoRgt).prod ≤ (ρ.plain.lhs.map dw_wNoRgt).prod := by decide
  have hP : ∀ π ∈ pairsPB, (π.rhs.map dw_wNoRgt).prod ≤ (π.lhs.map dw_wNoRgt).prod := by decide
  have hS : ∀ π ∈ pairsPB, GG (π.lhs.map dw_wNoRgt).prod (π.rhs.map dw_wNoRgt).prod := by
    unfold GG; decide
  exact h 1 Nat.one_pos (dw_wJA dw_wNoRgt) (fun s hs => Or.inr (hSF s hs))
    (fun ρ hρ => dw_weakA_wJA _ _ _ (hU ρ hρ)) (fun π hπ => dw_weakTop_wJA _ _ _ (hP π hπ))
    _ (List.mem_cons_self ..) (dw_strictTop_wJA _ _ _ (hS _ (List.mem_cons_self ..)))

/-- Reversed (`𝔸_ℕ`): false even if all symbols except `lft` are somewhere finite. -/
theorem dw_not_DPrev_noLft :
    ¬ BarrierDPFor (lettersPDrev.erase (DLetter.plain Letter.lft)) usableSTrev pairsPDrev := by
  intro h
  have hSF : ∀ s ∈ lettersPDrev.erase (DLetter.plain Letter.lft), dw_wNoLft s ≠ 0 := by decide
  have hU : ∀ ρ ∈ usableSTrev,
      (ρ.plain.rhs.map dw_wNoLft).prod ≤ (ρ.plain.lhs.map dw_wNoLft).prod := by decide
  have hP : ∀ π ∈ pairsPDrev, (π.rhs.map dw_wNoLft).prod ≤ (π.lhs.map dw_wNoLft).prod := by decide
  have hS : ∀ π ∈ pairsPDrev, GG (π.lhs.map dw_wNoLft).prod (π.rhs.map dw_wNoLft).prod := by
    unfold GG; decide
  exact h 1 Nat.one_pos (dw_wJA dw_wNoLft) (fun s hs => Or.inr (hSF s hs))
    (fun ρ hρ => dw_weakA_wJA _ _ _ (hU ρ hρ)) (fun π hπ => dw_weakTop_wJA _ _ _ (hP π hπ))
    _ (List.mem_cons_self ..) (dw_strictTop_wJA _ _ _ (hS _ (List.mem_cons_self ..)))

/-- Corollary: the form imposing somewhere finiteness on the marked symbol only is false (forward). -/
theorem dw_not_DP_markOnly : ¬ BarrierDPFor [DLetter.mark Letter.lft] usableST pairsPB :=
  fun h => dw_not_DP_noRgt (dw_barrierDPFor_mono (by decide) h)

/-- Corollary: the form imposing somewhere finiteness on the marked symbol only is false (reversed). -/
theorem dw_not_DPrev_markOnly : ¬ BarrierDPFor [DLetter.mark Letter.rgt] usableSTrev pairsPDrev :=
  fun h => dw_not_DPrev_noLft (dw_barrierDPFor_mono (by decide) h)

end Collatz.Arctic
