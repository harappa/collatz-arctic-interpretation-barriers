/-
Checks of the non-vacuity of the main statements (continued; §3 of `NonVacuity.lean`): tools for weight interpretations of dimension 1, and,
for each of the five statements, an interpretation satisfying all premises ((i)).
-/
import CollatzProof.Arctic.NonVacuity

namespace Collatz.Arctic

namespace NonVacuity

open Letter DLetter Matrix

/-! ## §3a Weight interpretations of dimension 1 (tools) -/

/-- Rule removal: dimension 1, `fin (w s)` for the symbol `s`. -/
def wI (w : Letter → ℕ) : Interp 1 := fun s _ _ => Arc.fin (w s)

theorem ev_wI (w : Letter → ℕ) (x : Word) (i j : Fin 1) :
    ev (wI w) x i j = Arc.fin (x.map w).sum := by
  induction x generalizing i j with
  | nil =>
    have hij : i = j := Subsingleton.elim i j
    subst hij
    simp only [ev, List.map_nil, List.prod_nil, Matrix.one_apply_eq, List.sum_nil]
    rfl
  | cons s x ih =>
    rw [ev_cons, Matrix.mul_apply, Fin.sum_univ_one, ih 0 j]
    simp only [wI, List.map_cons, List.sum_cons, Arc.fin_mul_fin]

theorem fin_ne_zero (n : ℕ) : Arc.fin n ≠ 0 := fun h => WithBot.coe_ne_bot h

theorem weak_wI (w : Letter → ℕ) (ρ : Rule) :
    Weak (wI w) ρ ↔ (ρ.rhs.map w).sum ≤ (ρ.lhs.map w).sum := by
  unfold Weak
  simp only [ev_wI, Arc.fin_le_fin]
  exact ⟨fun h => h 0 0, fun h _ _ => h⟩

theorem strict_wI (w : Letter → ℕ) (ρ : Rule) :
    Strict (wI w) ρ ↔ (ρ.rhs.map w).sum < (ρ.lhs.map w).sum := by
  unfold Strict
  simp only [ev_wI, Arc.fin_lt_fin]
  constructor
  · intro h
    rcases h 0 0 with h | ⟨h, _⟩
    · exact h
    · exact absurd h (fin_ne_zero _)
  · intro h _ _
    exact Or.inl h

theorem fin00_wI (w : Letter → ℕ) : Fin00 Nat.one_pos (wI w) := fun s => fin_ne_zero (w s)

/-- Dependency pairs (`𝔸_ℕ`): dimension 1, `x ↦ fin (w s) ⊗ x` for the symbol `s` (absolute part −∞). -/
def wJ (w : DLetter → ℕ) : DLetter → AffFun Arc 1 := fun s => ⟨fun _ _ => Arc.fin (w s), 0⟩

theorem evA_wJ (w : DLetter → ℕ) (x : List DLetter) :
    (∀ i j, (evA (wJ w) x).M i j = Arc.fin (x.map w).sum) ∧ (evA (wJ w) x).c = 0 := by
  induction x with
  | nil =>
    refine ⟨fun i j => ?_, rfl⟩
    have hij : i = j := Subsingleton.elim i j
    subst hij
    show (1 : AMat 1) i i = _
    simp only [Matrix.one_apply_eq, List.map_nil, List.sum_nil]
    rfl
  | cons s x ih =>
    obtain ⟨ihM, ihc⟩ := ih
    refine ⟨fun i j => ?_, ?_⟩
    · show ((wJ w s).M * (evA (wJ w) x).M) i j = _
      rw [Matrix.mul_apply, Fin.sum_univ_one, ihM]
      simp only [wJ, List.map_cons, List.sum_cons, Arc.fin_mul_fin]
    · show (wJ w s).M *ᵥ (evA (wJ w) x).c + (wJ w s).c = 0
      rw [ihc, Matrix.mulVec_zero, zero_add]
      rfl

theorem weakA_wJ (w : DLetter → ℕ) (u v : List DLetter) :
    WeakA (evA (wJ w) u) (evA (wJ w) v) ↔ (v.map w).sum ≤ (u.map w).sum := by
  unfold WeakA
  simp only [(evA_wJ w u).1, (evA_wJ w v).1, (evA_wJ w u).2, (evA_wJ w v).2, Arc.fin_le_fin]
  exact ⟨fun h => h.1 0 0, fun h => ⟨fun _ _ => h, fun _ => le_rfl⟩⟩

theorem weakTop_wJ (w : DLetter → ℕ) (u v : List DLetter) :
    WeakTop Nat.one_pos (evA (wJ w) u) (evA (wJ w) v) ↔ (v.map w).sum ≤ (u.map w).sum := by
  unfold WeakTop
  simp only [(evA_wJ w u).1, (evA_wJ w v).1, (evA_wJ w u).2, (evA_wJ w v).2, Arc.fin_le_fin]
  exact ⟨fun h => h.1 0, fun h => ⟨fun _ => h, le_rfl⟩⟩

theorem GG_fin (a b : ℕ) : GG (Arc.fin a) (Arc.fin b) ↔ b < a := by
  unfold GG
  rw [Arc.fin_lt_fin]
  exact ⟨fun h => h.resolve_right (fun h' => fin_ne_zero a h'.1), Or.inl⟩

theorem strictTop_wJ (w : DLetter → ℕ) (u v : List DLetter) :
    StrictTop Nat.one_pos (evA (wJ w) u) (evA (wJ w) v) ↔ (v.map w).sum < (u.map w).sum := by
  unfold StrictTop
  simp only [(evA_wJ w u).1, (evA_wJ w v).1, (evA_wJ w u).2, (evA_wJ w v).2, GG_fin]
  exact ⟨fun h => h.1 0, fun h => ⟨fun _ => h, Or.inr ⟨rfl, rfl⟩⟩⟩

theorem sf_wJ (w : DLetter → ℕ) (L : List DLetter) : SomewhereFinite Nat.one_pos (wJ w) L :=
  fun s _ => Or.inr (fin_ne_zero (w s))

/-- Dependency pairs (below zero `𝔸_ℤ`): dimension 1, `x ↦ fin (w s) ⊗ x ⊕ fin (w s)` for the symbol `s`
(`w s + max(x, 0)`, absolutely positive). -/
def wJZ (w : DLetter → ℕ) : DLetter → AffFun ArcZ 1 :=
  fun s => ⟨fun _ _ => ArcZ.fin (w s), fun _ => ArcZ.fin (w s)⟩

theorem ArcZ_fin_mul (a b : ℤ) : ArcZ.fin a * ArcZ.fin b = ArcZ.fin (a + b) :=
  ArcZ.ext (by simp only [ArcZ.val_mul, ArcZ.val_fin]; norm_cast)

theorem ArcZ_fin_add (a b : ℤ) : ArcZ.fin a + ArcZ.fin b = ArcZ.fin (max a b) :=
  ArcZ.ext (by simp only [ArcZ.val_add, ArcZ.val_fin]; exact (WithBot.coe_max a b).symm)

theorem ArcZ_fin_le (a b : ℤ) : ArcZ.fin a ≤ ArcZ.fin b ↔ a ≤ b := WithBot.coe_le_coe

theorem ArcZ_fin_lt (a b : ℤ) : ArcZ.fin a < ArcZ.fin b ↔ a < b := WithBot.coe_lt_coe

theorem ArcZ_fin_ne_zero (a : ℤ) : ArcZ.fin a ≠ 0 := fun h => WithBot.coe_ne_bot h

theorem evA_wJZ_M (w : DLetter → ℕ) (x : List DLetter) (i j : Fin 1) :
    (evA (wJZ w) x).M i j = ArcZ.fin ((x.map w).sum : ℕ) := by
  induction x generalizing i j with
  | nil =>
    have hij : i = j := Subsingleton.elim i j
    subst hij
    show (1 : Matrix (Fin 1) (Fin 1) ArcZ) i i = _
    simp only [Matrix.one_apply_eq, List.map_nil, List.sum_nil]
    rfl
  | cons s x ih =>
    show ((wJZ w s).M * (evA (wJZ w) x).M) i j = _
    rw [Matrix.mul_apply, Fin.sum_univ_one, ih 0 j]
    simp only [wJZ, List.map_cons, List.sum_cons, ArcZ_fin_mul, Nat.cast_add]

theorem evA_wJZ_c (w : DLetter → ℕ) (x : List DLetter) (i : Fin 1) :
    (evA (wJZ w) x).c i = if x = [] then 0 else ArcZ.fin ((x.map w).sum : ℕ) := by
  induction x generalizing i with
  | nil => rfl
  | cons s x ih =>
    show ((wJZ w s).M *ᵥ (evA (wJZ w) x).c + (wJZ w s).c) i = _
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_one, ih 0, wJZ,
      List.cons_ne_nil, ↓reduceIte, List.map_cons, List.sum_cons, Nat.cast_add]
    by_cases hx : x = []
    · subst hx
      simp
    · simp only [hx, ↓reduceIte, ArcZ_fin_mul, ArcZ_fin_add]
      rw [max_eq_left (by omega)]

theorem weakA_wJZ (w : DLetter → ℕ) {u v : List DLetter} (hu : u ≠ []) (hv : v ≠ []) :
    WeakA (evA (wJZ w) u) (evA (wJZ w) v) ↔ (v.map w).sum ≤ (u.map w).sum := by
  unfold WeakA
  simp only [evA_wJZ_M, evA_wJZ_c, hu, hv, ↓reduceIte, ArcZ_fin_le, Nat.cast_le]
  exact ⟨fun h => h.2 0, fun h => ⟨fun _ _ => h, fun _ => h⟩⟩

theorem weakTop_wJZ (w : DLetter → ℕ) {u v : List DLetter} (hu : u ≠ []) (hv : v ≠ []) :
    WeakTop Nat.one_pos (evA (wJZ w) u) (evA (wJZ w) v) ↔ (v.map w).sum ≤ (u.map w).sum := by
  unfold WeakTop
  simp only [evA_wJZ_M, evA_wJZ_c, hu, hv, ↓reduceIte, ArcZ_fin_le, Nat.cast_le]
  exact ⟨fun h => h.2, fun h => ⟨fun _ => h, h⟩⟩

theorem GGZ_fin (a b : ℤ) : GG (ArcZ.fin a) (ArcZ.fin b) ↔ b < a := by
  unfold GG
  rw [ArcZ_fin_lt]
  exact ⟨fun h => h.resolve_right (fun h' => ArcZ_fin_ne_zero a h'.1), Or.inl⟩

theorem strictTop_wJZ (w : DLetter → ℕ) {u v : List DLetter} (hu : u ≠ []) (hv : v ≠ []) :
    StrictTop Nat.one_pos (evA (wJZ w) u) (evA (wJZ w) v) ↔ (v.map w).sum < (u.map w).sum := by
  unfold StrictTop
  simp only [evA_wJZ_M, evA_wJZ_c, hu, hv, ↓reduceIte, GGZ_fin, Nat.cast_lt]
  exact ⟨fun h => h.2, fun h => ⟨fun _ => h, h⟩⟩

theorem ap_wJZ (w : DLetter → ℕ) (L : List DLetter) : AbsPositive Nat.one_pos (wJZ w) L :=
  fun s _ => (ArcZ_fin_le 0 (w s)).2 (by positivity)

/-- Both sides of the rules and dependency pairs are nonempty (a premise of the lemmas on `wJZ`). -/
theorem usableST_ne : ∀ ρ ∈ usableST, ρ.plain.lhs ≠ [] ∧ ρ.plain.rhs ≠ [] := by decide
theorem usableSTrev_ne : ∀ ρ ∈ usableSTrev, ρ.plain.lhs ≠ [] ∧ ρ.plain.rhs ≠ [] := by decide
theorem pairsPB_ne : ∀ π ∈ pairsPB, π.lhs ≠ [] ∧ π.rhs ≠ [] := by decide
theorem pairsPDrev_ne : ∀ π ∈ pairsPDrev, π.lhs ≠ [] ∧ π.rhs ≠ [] := by decide

/-! ## §3b (i) The premises are satisfiable -/

/-- A nontrivial weight (3 on `/`, 5 on `.`, 0 on the others). -/
def wLR : Letter → ℕ
  | lft => 3
  | rgt => 5
  | _ => 0

/-- All premises of `ArcticBarrierST` are satisfiable. -/
theorem hyp_ST_sat : ∃ (d : ℕ) (hd : 0 < d) (I : Interp d), Fin00 hd I ∧ ∀ ρ ∈ rulesST, Weak I ρ :=
  ⟨1, Nat.one_pos, wI wLR, fin00_wI _, fun ρ hρ => (weak_wI _ ρ).2 (by revert ρ; decide)⟩

/-- A weight for dependency pairs (2 on `/#`, `.#`, 3 on `/`, `.`, 0 on the others). -/
def wLRD : DLetter → ℕ
  | mark _ => 2
  | plain lft => 3
  | plain rgt => 3
  | _ => 0

theorem hyp_DP_sat : ∃ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun Arc d),
    SomewhereFinite hd J lettersPB ∧
    (∀ ρ ∈ usableST, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) :=
  ⟨1, Nat.one_pos, wJ wLRD, sf_wJ _ _,
    fun ρ hρ => (weakA_wJ _ _ _).2 (by revert ρ; decide),
    fun π hπ => (weakTop_wJ _ _ _).2 (by revert π; decide)⟩

theorem hyp_DPrev_sat : ∃ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun Arc d),
    SomewhereFinite hd J lettersPDrev ∧
    (∀ ρ ∈ usableSTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ pairsPDrev, WeakTop hd (evA J π.lhs) (evA J π.rhs)) :=
  ⟨1, Nat.one_pos, wJ wLRD, sf_wJ _ _,
    fun ρ hρ => (weakA_wJ _ _ _).2 (by revert ρ; decide),
    fun π hπ => (weakTop_wJ _ _ _).2 (by revert π; decide)⟩

theorem hyp_BZ_sat : ∃ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d),
    AbsPositive hd J lettersPB ∧
    (∀ ρ ∈ usableST, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) :=
  ⟨1, Nat.one_pos, wJZ wLRD, ap_wJZ _ _,
    fun ρ hρ => (weakA_wJZ _ (usableST_ne ρ hρ).1 (usableST_ne ρ hρ).2).2 (by revert ρ; decide),
    fun π hπ => (weakTop_wJZ _ (pairsPB_ne π hπ).1 (pairsPB_ne π hπ).2).2 (by revert π; decide)⟩

theorem hyp_BZrev_sat : ∃ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d),
    AbsPositive hd J lettersPDrev ∧
    (∀ ρ ∈ usableSTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ pairsPDrev, WeakTop hd (evA J π.lhs) (evA J π.rhs)) :=
  ⟨1, Nat.one_pos, wJZ wLRD, ap_wJZ _ _,
    fun ρ hρ => (weakA_wJZ _ (usableSTrev_ne ρ hρ).1 (usableSTrev_ne ρ hρ).2).2
      (by revert ρ; decide),
    fun π hπ => (weakTop_wJZ _ (pairsPDrev_ne π hπ).1 (pairsPDrev_ne π hπ).2).2
      (by revert π; decide)⟩

end NonVacuity

end Collatz.Arctic
