/-
Proofs of the weakened-premise forms of the arctic barriers for dependency pairs (continued from `DPWeak.lean`; Proposition 4.1,
weakened-premise forms of Theorems 3.3 and 3.4).

* The core lemmas below zero `dw_BZ_core`, `dw_BZrev_core`: if the values are uniformly bounded below (`V ≥ C`, `C ∈ ℤ`), the barrier holds
  (the proof of `BZMain.lean` with the natural-number property `Vw_nat` replaced by the lower bound and the translation `dw_barrier_of_lb`).
* The proofs from the weak premises, `dw_barrier_DPw` etc. (from `AutoCore`), and the unconditional main theorems
  `arcticBarrierDPw`, `arcticBarrierDPrevw`, `arcticBarrierBZf`, `arcticBarrierBZrevf`,
  `arcticBarrierBZw`, `arcticBarrierBZrevw`.
* Implications (inclusions of premises): `BZf → BZw → BZ`, `DPw → DP` (also reversed). The frozen statements follow as corollaries
  of the weak forms.
-/
import CollatzProof.Arctic.DPWeak

namespace Collatz.Arctic

open Matrix

/-! ## Core lemmas below zero (with a lower bound of values as a hypothesis) -/

/-- Forward (below zero): if the values are uniformly bounded below, the barrier holds. -/
theorem dw_BZ_core (hcore : AutoCore) {d : ℕ} (hd : 0 < d) (J : DLetter → AffFun ArcZ d)
    (hU : ∀ ρ ∈ usableST, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs))
    (hP : ∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs))
    (hlb : ∃ C : ℤ, ∀ n, ArcZ.fin C ≤ Vw hd J Letter.lft (binTail n ++ [Letter.rgt])) :
    ∀ π ∈ pairsPB, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs) := by
  intro π hπ hs
  rw [pairsPB_eq] at hπ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hπ
  have hPw : ∀ ρ ∈ rootPB, WeakTop hd (evA J (dp Letter.lft ρ).lhs) (evA J (dp Letter.lft ρ).rhs) :=
    fun ρ hρ => hP _ (by rw [pairsPB_eq]; exact List.mem_map_of_mem hρ)
  have hσU : σ ∉ usableST := by
    simp only [rootPB, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl | rfl <;> decide
  have hσST : σ ∈ rulesST := by
    simp only [rootPB, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl | rfl <;> decide
  obtain ⟨C, hC⟩ := hlb
  refine dw_barrier_of_lb hcore (fun j => hom (J (DLetter.mark Letter.lft)) (c0 hd) j)
    (homL J) (homL J Letter.rgt *ᵥ xs hd) σ hσST C ?_ ?_
  · intro n
    rw [autoValZ, ← Vw_fwd_eq]
    exact hC n
  · intro n hn
    have := Vw_chain hd J Letter.lft (ArcZ.fin 1) (fun _ _ h => ArcZ.gg_mul_fin_one h) hU hPw hσU
      hs (dcanDeriv n hn)
    rwa [Vw_fwd_eq, Vw_fwd_eq] at this

/-- Reversed (below zero): the same. -/
theorem dw_BZrev_core (hcore : AutoCore) {d : ℕ} (hd : 0 < d) (J : DLetter → AffFun ArcZ d)
    (hU : ∀ ρ ∈ usableSTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs))
    (hP : ∀ π ∈ pairsPDrev, WeakTop hd (evA J π.lhs) (evA J π.rhs))
    (hlb : ∃ C : ℤ, ∀ n, ArcZ.fin C ≤ Vw hd J Letter.rgt ((binTail n).reverse ++ [Letter.lft])) :
    ∀ π ∈ pairsPDrev, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs) := by
  intro π hπ hs
  rw [pairsPDrev_eq] at hπ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hπ
  have hPw : ∀ ρ ∈ rootPDrev,
      WeakTop hd (evA J (dp Letter.rgt ρ).lhs) (evA J (dp Letter.rgt ρ).rhs) :=
    fun ρ hρ => hP _ (by rw [pairsPDrev_eq]; exact List.mem_map_of_mem hρ)
  have hσU : σ ∉ usableSTrev := by
    simp only [rootPDrev, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl <;> decide
  obtain ⟨τ, hτ, rfl⟩ := rootPDrev_mem hσ
  obtain ⟨C, hC⟩ := hlb
  refine dw_barrier_of_lb hcore (homL J Letter.lft *ᵥ xs hd) (fun s => (homL J s)ᵀ)
    (fun j => hom (J (DLetter.mark Letter.rgt)) (c0 hd) j) τ hτ C ?_ ?_
  · intro n
    rw [autoValZ, ← Vw_rev_eq]
    exact hC n
  · intro n hn
    have := Vw_chain hd J Letter.rgt (ArcZ.fin 1) (fun _ _ h => ArcZ.gg_mul_fin_one h) hU hPw hσU
      hs (dcanDeriv_rev n hn)
    rwa [Vw_rev_eq, Vw_rev_eq, count_rev] at this

/-! ## Proofs from the weak premises (from `AutoCore`) -/

theorem dw_barrier_DPw (hcore : AutoCore) : ArcticBarrierDPw := fun _ hd J hSF hU hP =>
  dw_DP_core hcore hd J hU hP (fun _ n => dw_Vw_ne_zero hd J _ _ hSF _ (dw_fwd_letters n))

theorem dw_barrier_DPrevw (hcore : AutoCore) : ArcticBarrierDPrevw := fun _ hd J hSF hU hP =>
  dw_DPrev_core hcore hd J hU hP (fun _ n => dw_Vw_ne_zero hd J _ _ hSF _ (dw_rev_letters n))

theorem dw_barrier_BZf (hcore : AutoCore) : ArcticBarrierBZf := by
  intro d hd J hF hU hP
  obtain ⟨C, hC⟩ := dw_Vw_lb hd J Letter.lft Letter.rgt hF
  exact dw_BZ_core hcore hd J hU hP ⟨C, fun n => hC _ (by simp) (dw_fwd_letters n)⟩

theorem dw_barrier_BZrevf (hcore : AutoCore) : ArcticBarrierBZrevf := by
  intro d hd J hF hU hP
  obtain ⟨C, hC⟩ := dw_Vw_lb hd J Letter.rgt Letter.lft hF
  exact dw_BZrev_core hcore hd J hU hP ⟨C, fun n => hC _ (by simp) (dw_rev_letters n)⟩

/-! ## Implications (inclusions of premises) -/

/-- If `0 ≤ a`, then `a` is finite. -/
lemma dw_ne_zero_of_nonneg {a : ArcZ} (h : ArcZ.fin 0 ≤ a) : a ≠ 0 := by
  intro h0; rw [h0, ArcZ.le_iff_val] at h; simp at h

/-- The weak condition from somewhere finiteness of the symbols occurring in the problem. -/
lemma dw_SFRoot_of_SF {d : ℕ} (hd : 0 < d) (J : DLetter → AffFun Arc d) (h e : Letter)
    (L : List DLetter)
    (hL : ∀ s ∈ [DLetter.mark h, DLetter.plain Letter.f, DLetter.plain Letter.t, DLetter.plain e],
      s ∈ L) (hSF : SomewhereFinite hd J L) : SFRoot hd J h e :=
  Or.inr (fun s hs => hSF s (hL s hs))

theorem DP_of_DPw (h : ArcticBarrierDPw) : ArcticBarrierDP := fun d hd J hSF =>
  h d hd J (dw_SFRoot_of_SF hd J _ _ _ (by decide) hSF)

theorem DPrev_of_DPrevw (h : ArcticBarrierDPrevw) : ArcticBarrierDPrev := fun d hd J hSF =>
  h d hd J (dw_SFRoot_of_SF hd J _ _ _ (by decide) hSF)

theorem BZw_of_BZf (h : ArcticBarrierBZf) : ArcticBarrierBZw := fun d hd J hAP =>
  h d hd J (Or.inl (dw_ne_zero_of_nonneg (hAP _ (by simp))))

theorem BZrevw_of_BZrevf (h : ArcticBarrierBZrevf) : ArcticBarrierBZrevw := fun d hd J hAP =>
  h d hd J (Or.inl (dw_ne_zero_of_nonneg (hAP _ (by simp))))

theorem BZ_of_BZw (h : ArcticBarrierBZw) : ArcticBarrierBZ := fun d hd J hAP =>
  h d hd J (fun s hs => hAP s (by rw [List.mem_singleton] at hs; subst hs; decide))

theorem BZrev_of_BZrevw (h : ArcticBarrierBZrevw) : ArcticBarrierBZrev := fun d hd J hAP =>
  h d hd J (fun s hs => hAP s (by rw [List.mem_singleton] at hs; subst hs; decide))

/-! ## Unconditional main theorems -/

/-- `AutoCore` (from the same three proofs `hsp_holds`, `hKeyTop`, `hLeftUse` as in `Summary.lean`). -/
theorem dw_autoCore : AutoCore := autoCore_of_hyps hsp_holds (hTerrasWin_of_key hKeyTop) hLeftUse

/-- **Theorem 3.3 (forward, `𝔸_ℕ`), weak premise `SFRoot`** (Proposition 4.1). -/
theorem arcticBarrierDPw : ArcticBarrierDPw := dw_barrier_DPw dw_autoCore
/-- **Theorem 3.3 (reversed, `𝔸_ℕ`), weak premise `SFRoot`** (Proposition 4.1). -/
theorem arcticBarrierDPrevw : ArcticBarrierDPrevw := dw_barrier_DPrevw dw_autoCore
/-- **Theorem 3.4 (forward, below zero), weakest premise `FinRootZ`** (Proposition 4.1). -/
theorem arcticBarrierBZf : ArcticBarrierBZf := dw_barrier_BZf dw_autoCore
/-- **Theorem 3.4 (reversed, below zero), weakest premise `FinRootZ`** (Proposition 4.1). -/
theorem arcticBarrierBZrevf : ArcticBarrierBZrevf := dw_barrier_BZrevf dw_autoCore
/-- **Theorem 3.4 (forward, below zero), absolute positivity of `lft#` only** (Proposition 4.1). -/
theorem arcticBarrierBZw : ArcticBarrierBZw := BZw_of_BZf arcticBarrierBZf
/-- **Theorem 3.4 (reversed, below zero), absolute positivity of `rgt#` only** (Proposition 4.1). -/
theorem arcticBarrierBZrevw : ArcticBarrierBZrevw := BZrevw_of_BZrevf arcticBarrierBZrevf

/-- The frozen statements are corollaries of the weak forms (a proof by a route different from that of `Summary.lean`). -/
theorem dw_frozen_of_weak : ArcticBarrierDP ∧ ArcticBarrierDPrev ∧ ArcticBarrierBZ ∧
    ArcticBarrierBZrev :=
  ⟨DP_of_DPw arcticBarrierDPw, DPrev_of_DPrevw arcticBarrierDPrevw, BZ_of_BZw arcticBarrierBZw,
    BZrev_of_BZrevw arcticBarrierBZrevw⟩

end Collatz.Arctic
