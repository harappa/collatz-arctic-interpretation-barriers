/-
Checks of the weakened-premise statements (`DPWeak.lean` to `DPWeak3.lean`), continued: non-vacuity (§2) and the form under the Collatz conjecture
(§3, Proposition 4.6). All interpretations have dimension 1.

* §2a All weak premises are satisfiable (from the interpretations for the frozen statements, `NonVacuity2.hyp_DP_sat` etc.).
* §2b Interpretations that satisfy the weak premises but not the original ones (all unmarked symbols the constant −∞, `h#` a finite constant).
  `SFRoot` is strictly weaker than somewhere finiteness of `lettersPB`, and `FinRootZ` than absolute positivity of `h#`, which in turn is strictly weaker than
  absolute positivity of `lettersPB`. Hence the weakened statements are strictly stronger than the frozen ones.
* §3 The form `ArcticBarrierDPmin` over `𝔸_ℕ` that also drops somewhere finiteness of `f`, `t` (only `lft#` and `rgt`; reversed: `rgt#` and
  `lft`) holds if every `n ≥ 1` reaches 1 under `T` (`dw_barrier_DPmin_of_reach`). `V(1)` is finite and
  values do not increase along `T`-steps, so the value of every `n` that reaches 1 is finite and `AutoCore` applies. Hence a counterexample to this form gives an orbit that does not reach
  1 (`dw_not_reach_of_not_DPmin`). Showing by a counterexample that the conditions on `f`, `t` are needed requires disproving the Collatz conjecture, and
  an unconditional proof of this form needs another argument giving finiteness of values independently of orbits (both open). The counterexample of `DPWeak3.lean`
  (−∞ on `rgt`) does not satisfy the premises of this form.
-/
import CollatzProof.Arctic.DPWeak3

namespace Collatz.Arctic

open Matrix NonVacuity

/-! ## §2a The weak premises are satisfiable -/

theorem dw_hyp_DPw_sat : ∃ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun Arc d),
    SFRoot hd J Letter.lft Letter.rgt ∧
    (∀ ρ ∈ usableST, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) := by
  obtain ⟨d, hd, J, hSF, hU, hP⟩ := hyp_DP_sat
  exact ⟨d, hd, J, dw_SFRoot_of_SF hd J _ _ _ (by decide) hSF, hU, hP⟩

theorem dw_hyp_DPrevw_sat : ∃ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun Arc d),
    SFRoot hd J Letter.rgt Letter.lft ∧
    (∀ ρ ∈ usableSTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ pairsPDrev, WeakTop hd (evA J π.lhs) (evA J π.rhs)) := by
  obtain ⟨d, hd, J, hSF, hU, hP⟩ := hyp_DPrev_sat
  exact ⟨d, hd, J, dw_SFRoot_of_SF hd J _ _ _ (by decide) hSF, hU, hP⟩

theorem dw_hyp_BZw_sat : ∃ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d),
    AbsPositive hd J [DLetter.mark Letter.lft] ∧
    (∀ ρ ∈ usableST, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) := by
  obtain ⟨d, hd, J, hAP, hU, hP⟩ := hyp_BZ_sat
  exact ⟨d, hd, J, fun s hs => hAP s (by rw [List.mem_singleton] at hs; subst hs; decide), hU, hP⟩

theorem dw_hyp_BZrevw_sat : ∃ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d),
    AbsPositive hd J [DLetter.mark Letter.rgt] ∧
    (∀ ρ ∈ usableSTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ pairsPDrev, WeakTop hd (evA J π.lhs) (evA J π.rhs)) := by
  obtain ⟨d, hd, J, hAP, hU, hP⟩ := hyp_BZrev_sat
  exact ⟨d, hd, J, fun s hs => hAP s (by rw [List.mem_singleton] at hs; subst hs; decide), hU, hP⟩

/-! ## §2b The weak premises are strictly weaker -/

/-- The interpretation with the marked symbols as the constant `κ` and the unmarked symbols as the constant −∞ (all matrices are −∞). -/
def dw_Jconst {R : Type} [CommSemiring R] {d : ℕ} (κ : Fin d → R) : DLetter → AffFun R d
  | DLetter.mark _ => ⟨0, κ⟩
  | DLetter.plain _ => ⟨0, 0⟩

lemma dw_evA_Jconst_cons {R : Type} [CommSemiring R] {d : ℕ} (κ : Fin d → R) (s : DLetter)
    (L : List DLetter) : evA (dw_Jconst κ) (s :: L) = ⟨0, (dw_Jconst κ s).c⟩ := by
  rw [dw_evA_cons]
  cases s <;> simp [dw_Jconst, AffFun.comp]

lemma dw_Jconst_U {R : Type} [CommSemiring R] [LinearOrder R] {d : ℕ} (κ : Fin d → R)
    (U : List Rule) (hU : ∀ ρ ∈ U, ρ.lhs ≠ [] ∧ ρ.rhs ≠ []) :
    ∀ ρ ∈ U, WeakA (evA (dw_Jconst κ) ρ.plain.lhs) (evA (dw_Jconst κ) ρ.plain.rhs) := by
  intro ρ hρ
  obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil (hU ρ hρ).1
  obtain ⟨b, r, hr⟩ := List.exists_cons_of_ne_nil (hU ρ hρ).2
  show WeakA (evA _ (ρ.lhs.map _)) (evA _ (ρ.rhs.map _))
  rw [hl, hr, List.map_cons, List.map_cons, dw_evA_Jconst_cons, dw_evA_Jconst_cons]
  exact ⟨fun _ _ => le_rfl, fun _ => le_rfl⟩

lemma dw_Jconst_P {R : Type} [CommSemiring R] [LinearOrder R] {d : ℕ} (hd : 0 < d)
    (κ : Fin d → R) (P : List DRule) (h : Letter)
    (hP : ∀ π ∈ P, π.lhs.head? = some (DLetter.mark h) ∧ π.rhs.head? = some (DLetter.mark h)) :
    ∀ π ∈ P, WeakTop hd (evA (dw_Jconst κ) π.lhs) (evA (dw_Jconst κ) π.rhs) := by
  intro π hπ
  obtain ⟨hl, hr⟩ := hP π hπ
  rcases hL : π.lhs with _ | ⟨a, l⟩
  · rw [hL] at hl; simp at hl
  rcases hR : π.rhs with _ | ⟨b, r⟩
  · rw [hR] at hr; simp at hr
  rw [hL] at hl; rw [hR] at hr
  simp only [List.head?_cons, Option.some.injEq] at hl hr
  subst hl hr
  rw [dw_evA_Jconst_cons, dw_evA_Jconst_cons]
  exact ⟨fun _ => le_rfl, le_rfl⟩

/-- `𝔸_ℕ`, forward: an interpretation that satisfies `SFRoot` but not somewhere finiteness of `lettersPB`. -/
theorem dw_hyp_DPw_new : ∃ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun Arc d),
    SFRoot hd J Letter.lft Letter.rgt ∧ ¬ SomewhereFinite hd J lettersPB ∧
    (∀ ρ ∈ usableST, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) := by
  refine ⟨1, Nat.one_pos, dw_Jconst (fun _ => Arc.fin 0), Or.inl (fin_ne_zero 0), fun h => ?_,
    dw_Jconst_U _ _ dw_usableST_ne, dw_Jconst_P _ _ _ _ dw_pairsPB_head⟩
  have := h (DLetter.plain Letter.f) (by decide)
  simp [dw_Jconst] at this

/-- `𝔸_ℕ`, reversed: the same. -/
theorem dw_hyp_DPrevw_new : ∃ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun Arc d),
    SFRoot hd J Letter.rgt Letter.lft ∧ ¬ SomewhereFinite hd J lettersPDrev ∧
    (∀ ρ ∈ usableSTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ pairsPDrev, WeakTop hd (evA J π.lhs) (evA J π.rhs)) := by
  refine ⟨1, Nat.one_pos, dw_Jconst (fun _ => Arc.fin 0), Or.inl (fin_ne_zero 0), fun h => ?_,
    dw_Jconst_U _ _ dw_usableSTrev_ne, dw_Jconst_P _ _ _ _ dw_pairsPDrev_head⟩
  have := h (DLetter.plain Letter.f) (by decide)
  simp [dw_Jconst] at this

/-- Below zero, forward: the absolute part of `h#` is negative (`−1`); `FinRootZ` holds but absolute positivity of `lft#` fails. -/
theorem dw_hyp_BZf_new : ∃ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d),
    FinRootZ hd J Letter.lft Letter.rgt ∧ ¬ AbsPositive hd J [DLetter.mark Letter.lft] ∧
    (∀ ρ ∈ usableST, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) := by
  refine ⟨1, Nat.one_pos, dw_Jconst (fun _ => ArcZ.fin (-1)), Or.inl (ArcZ_fin_ne_zero (-1)),
    fun h => ?_, dw_Jconst_U _ _ dw_usableST_ne, dw_Jconst_P _ _ _ _ dw_pairsPB_head⟩
  have := (ArcZ_fin_le 0 (-1)).1 (h (DLetter.mark Letter.lft) (by simp))
  omega

/-- Below zero, forward: absolute positivity of `lft#` holds but that of `lettersPB` fails. -/
theorem dw_hyp_BZw_new : ∃ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d),
    AbsPositive hd J [DLetter.mark Letter.lft] ∧ ¬ AbsPositive hd J lettersPB ∧
    (∀ ρ ∈ usableST, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) := by
  refine ⟨1, Nat.one_pos, dw_Jconst (fun _ => ArcZ.fin 0),
    fun s hs => by rw [List.mem_singleton] at hs; subst hs; exact le_rfl,
    fun h => dw_ne_zero_of_nonneg (h (DLetter.plain Letter.f) (by decide)) rfl,
    dw_Jconst_U _ _ dw_usableST_ne, dw_Jconst_P _ _ _ _ dw_pairsPB_head⟩

/-- Below zero, reversed: `FinRootZ` holds but absolute positivity of `rgt#` fails. -/
theorem dw_hyp_BZrevf_new : ∃ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d),
    FinRootZ hd J Letter.rgt Letter.lft ∧ ¬ AbsPositive hd J [DLetter.mark Letter.rgt] ∧
    (∀ ρ ∈ usableSTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ pairsPDrev, WeakTop hd (evA J π.lhs) (evA J π.rhs)) := by
  refine ⟨1, Nat.one_pos, dw_Jconst (fun _ => ArcZ.fin (-1)), Or.inl (ArcZ_fin_ne_zero (-1)),
    fun h => ?_, dw_Jconst_U _ _ dw_usableSTrev_ne, dw_Jconst_P _ _ _ _ dw_pairsPDrev_head⟩
  have := (ArcZ_fin_le 0 (-1)).1 (h (DLetter.mark Letter.rgt) (by simp))
  omega

/-- Below zero, reversed: absolute positivity of `rgt#` holds but that of `lettersPDrev` fails. -/
theorem dw_hyp_BZrevw_new : ∃ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d),
    AbsPositive hd J [DLetter.mark Letter.rgt] ∧ ¬ AbsPositive hd J lettersPDrev ∧
    (∀ ρ ∈ usableSTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) ∧
    (∀ π ∈ pairsPDrev, WeakTop hd (evA J π.lhs) (evA J π.rhs)) := by
  refine ⟨1, Nat.one_pos, dw_Jconst (fun _ => ArcZ.fin 0),
    fun s hs => by rw [List.mem_singleton] at hs; subst hs; exact le_rfl,
    fun h => dw_ne_zero_of_nonneg (h (DLetter.plain Letter.f) (by decide)) rfl,
    dw_Jconst_U _ _ dw_usableSTrev_ne, dw_Jconst_P _ _ _ _ dw_pairsPDrev_head⟩

/-! ## §3 The form under the Collatz conjecture (dropping also the conditions on `f`, `t`) -/

/-- Every `n ≥ 1` reaches 1 under `T` (the Collatz conjecture stated with `T`). -/
def CollatzReachT : Prop := ∀ n, 1 ≤ n → ∃ k, T^[k] n = 1

/-- The form of Theorem 3.3 (forward, `𝔸_ℕ`) that also drops somewhere finiteness of `f`, `t` (only `lft#` and `rgt`). -/
def ArcticBarrierDPmin : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun Arc d),
    SomewhereFinite hd J [DLetter.mark Letter.lft, DLetter.plain Letter.rgt] →
    (∀ ρ ∈ usableST, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPB, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-- The form of Theorem 3.3 (reversed, `𝔸_ℕ`) that also drops somewhere finiteness of `f`, `t` (only `rgt#` and `lft`). -/
def ArcticBarrierDPrevmin : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun Arc d),
    SomewhereFinite hd J [DLetter.mark Letter.rgt, DLetter.plain Letter.lft] →
    (∀ ρ ∈ usableSTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPDrev, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPDrev, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

lemma dw_one_le_T (n : ℕ) (hn : 2 ≤ n) : 1 ≤ T n := by
  unfold T; split_ifs <;> omega

/-- Values of points that reach 1 are finite: if `V(1)` is finite and values do not increase along `T`-steps (after multiplication by an arctic power of 1),
then `V(n)` is finite for every `n ≥ 1` with `T^k(n) = 1`. -/
lemma dw_fin_of_reach (V : ℕ → Arc) (h1 : V 1 ≠ 0)
    (hstep : ∀ n, 2 ≤ n → ∃ k, V (T n) * Arc.fin 1 ^ k ≤ V n) :
    ∀ k n, 1 ≤ n → T^[k] n = 1 → V n ≠ 0 := by
  intro k
  induction k with
  | zero => intro n _ hn; rw [Function.iterate_zero_apply] at hn; subst hn; exact h1
  | succ k ih =>
    intro n hn1 hk
    by_cases hn : n = 1
    · subst hn; exact h1
    · have hn2 : 2 ≤ n := by omega
      rw [Function.iterate_succ_apply] at hk
      obtain ⟨k', hk'⟩ := hstep n hn2
      refine Arc.ne_zero_of_le hk' (Arc.mul_ne_zero' (ih (T n) (dw_one_le_T n hn2) hk) ?_)
      rw [Arc.fin_one_pow]; exact fin_ne_zero k'

lemma dw_binTail_zero : binTail 0 = binTail 1 := by decide

/-- **Under the Collatz conjecture**, the forward form without the conditions on `f`, `t` holds. -/
theorem dw_barrier_DPmin_of_reach (hC : CollatzReachT) : ArcticBarrierDPmin := by
  intro d hd J hSF hU hP
  refine dw_DP_core dw_autoCore hd J hU hP (fun hstep n => ?_)
  have h1 : Vw hd J Letter.lft (binTail 1 ++ [Letter.rgt]) ≠ 0 :=
    Vw_ne_zero hd J _ hSF Letter.lft (by simp) _ (by rw [binTail_one]; simp)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [dw_binTail_zero]; exact h1
  · obtain ⟨k, hk⟩ := hC n hn
    exact dw_fin_of_reach (fun n => Vw hd J Letter.lft (binTail n ++ [Letter.rgt])) h1 hstep
      k n hn hk

/-- **Under the Collatz conjecture**, the reversed form without the conditions on `f`, `t` holds. -/
theorem dw_barrier_DPrevmin_of_reach (hC : CollatzReachT) : ArcticBarrierDPrevmin := by
  intro d hd J hSF hU hP
  refine dw_DPrev_core dw_autoCore hd J hU hP (fun hstep n => ?_)
  have h1 : Vw hd J Letter.rgt ((binTail 1).reverse ++ [Letter.lft]) ≠ 0 :=
    Vw_ne_zero hd J _ hSF Letter.rgt (by simp) _ (by rw [binTail_one]; simp)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [dw_binTail_zero]; exact h1
  · obtain ⟨k, hk⟩ := hC n hn
    exact dw_fin_of_reach (fun n => Vw hd J Letter.rgt ((binTail n).reverse ++ [Letter.lft])) h1
      hstep k n hn hk

/-- Contrapositive: if the forward form without the conditions on `f`, `t` has a counterexample, then some `n ≥ 1` does not reach 1 under `T`. -/
theorem dw_not_reach_of_not_DPmin (h : ¬ ArcticBarrierDPmin) : ¬ CollatzReachT :=
  fun hC => h (dw_barrier_DPmin_of_reach hC)

/-- Contrapositive (reversed). -/
theorem dw_not_reach_of_not_DPrevmin (h : ¬ ArcticBarrierDPrevmin) : ¬ CollatzReachT :=
  fun hC => h (dw_barrier_DPrevmin_of_reach hC)

end Collatz.Arctic
