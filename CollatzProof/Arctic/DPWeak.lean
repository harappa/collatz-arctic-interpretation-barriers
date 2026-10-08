/-
Weakened-premise forms of the arctic barriers for dependency pairs, and their proofs (Proposition 4.1: weakened-premise forms of
Theorems 3.3 and 3.4). The frozen statements (`DPStatement.lean`) are not changed; the new forms are separate definitions.

* The frozen statements impose somewhere finiteness (`𝔸_ℕ`) or absolute positivity (below zero) on all symbols occurring in the problem
  (`lettersPB`, `lettersPDrev`). The proofs (`DPMain.lean`, `BZMain.lean`) use this at one place only: that the value
  `V(n) = ([h# bin'(n) e](x*))₁` is finite (`𝔸_ℕ`) or a natural number (below zero); the symbols involved are the marked
  symbol `h#` and the symbols `f`, `t` and the end symbol `e` of the value string (forward `h = lft`, `e = rgt`; reversed `h = rgt`, `e = lft`).
  The digit symbols `d0..d2` and the other end symbol are not involved.
* The weak condition `SFRoot` for `𝔸_ℕ`: the first component of the absolute part of `h#` is finite (then no condition on other symbols is needed; the value is
  at least `c_{h#}[1]`), or `h#`, `f`, `t`, `e` are somewhere finite (the argument of Koprowski–Waldmann 2009, Lemma 6.2).
* The weak condition `FinRootZ` below zero: the first component of the absolute part of `h#` is finite (**not necessarily ≥ 0**), or the `(1,1)`
  entry of `h#` is finite and the first components of the absolute parts of `f`, `t`, `e` are finite. In either case the value is bounded below (`V ≥ C`, `C ∈ ℤ`), and a translation by `C`
  makes it a natural number (`dw_barrier_of_lb`). The form that imposes absolute positivity on the marked symbol only
  (`ArcticBarrierBZw`, the condition of Koprowski–Waldmann 2009, Definition 8.1, restricted to `h#`) is a special case.
* **Premises that cannot be dropped** (Proposition 4.2): the condition on the marked symbol (in all four statements), and, over `𝔸_ℕ` when only the `(1,1)` entry of `h#` is finite,
  somewhere finiteness of the end symbol `e` (counterexamples in `DPWeak3.lean`). Hence the form that imposes somewhere finiteness on the marked symbol only
  is false. The conditions on `f`, `t` can be dropped if every `n ≥ 1` reaches 1 under `T` (`DPWeak4.lean`, Proposition 4.6).
* This file: the weak premises and statements, finiteness and lower bounds of values, the translation `dw_barrier_of_lb` from a lower bound below zero, and the core
  lemmas for `𝔸_ℕ`, `dw_DP_core` and `dw_DPrev_core` (barriers with finiteness of values as a hypothesis).
* `DPWeak2.lean`: the core lemmas below zero, the unconditional main theorems (with `AutoCore` from the same three
  proofs as in `Summary.lean`) `arcticBarrierDPw`, `arcticBarrierDPrevw`, `arcticBarrierBZf`, `arcticBarrierBZrevf`, their corollaries
  `arcticBarrierBZw`, `arcticBarrierBZrevw`, and the implications to the frozen statements such as `DP_of_DPw`.
* `DPWeak3.lean`: counterexamples for the premises that cannot be dropped. `DPWeak4.lean`: non-vacuity, and the form under the Collatz conjecture.
-/
import CollatzProof.Arctic.Summary

namespace Collatz.Arctic

open Matrix

/-! ## Weak premises and statements -/

/-- The weak finiteness condition for `𝔸_ℕ` (marked symbol `h#`, end symbol `e` of the value string): the first component of the absolute part of `h#`
is finite, or `h#`, `f`, `t`, `e` are somewhere finite. -/
def SFRoot {d : ℕ} (hd : 0 < d) (J : DLetter → AffFun Arc d) (h e : Letter) : Prop :=
  (J (DLetter.mark h)).c ⟨0, hd⟩ ≠ 0 ∨
    SomewhereFinite hd J
      [DLetter.mark h, DLetter.plain Letter.f, DLetter.plain Letter.t, DLetter.plain e]

/-- The weak condition below zero: the first component of the absolute part of `h#` is finite (of any sign), or the `(1,1)` entry of `h#` is finite and
the first components of the absolute parts of `f`, `t`, `e` are finite. -/
def FinRootZ {d : ℕ} (hd : 0 < d) (J : DLetter → AffFun ArcZ d) (h e : Letter) : Prop :=
  (J (DLetter.mark h)).c ⟨0, hd⟩ ≠ 0 ∨
    ((J (DLetter.mark h)).M ⟨0, hd⟩ ⟨0, hd⟩ ≠ 0 ∧
      ∀ s ∈ [Letter.f, Letter.t, e], (J (DLetter.plain s)).c ⟨0, hd⟩ ≠ 0)

/-- **Weakened-premise form of Theorem 3.3 ($\mathcal T$, forward, `𝔸_ℕ`)**: only `SFRoot` (`lft#`, end `rgt`) is imposed. -/
def ArcticBarrierDPw : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun Arc d), SFRoot hd J Letter.lft Letter.rgt →
    (∀ ρ ∈ usableST, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPB, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-- **Weakened-premise form of Theorem 3.3 ($\mathcal T$, reversed, `𝔸_ℕ`)**: only `SFRoot` (`rgt#`, end `lft`) is imposed. -/
def ArcticBarrierDPrevw : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun Arc d), SFRoot hd J Letter.rgt Letter.lft →
    (∀ ρ ∈ usableSTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPDrev, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPDrev, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-- **Form of Theorem 3.4 ($\mathcal T$, forward, below zero) with absolute positivity imposed on the marked symbol only**. -/
def ArcticBarrierBZw : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d), AbsPositive hd J [DLetter.mark Letter.lft] →
    (∀ ρ ∈ usableST, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPB, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-- **Form of Theorem 3.4 ($\mathcal T$, reversed, below zero) with absolute positivity imposed on the marked symbol only**. -/
def ArcticBarrierBZrevw : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d), AbsPositive hd J [DLetter.mark Letter.rgt] →
    (∀ ρ ∈ usableSTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPDrev, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPDrev, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-- **Weakest form of Theorem 3.4 (forward, below zero)**: only `FinRootZ` (`lft#`, end `rgt`) is imposed. -/
def ArcticBarrierBZf : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d), FinRootZ hd J Letter.lft Letter.rgt →
    (∀ ρ ∈ usableST, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPB, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-- **Weakest form of Theorem 3.4 (reversed, below zero)**: only `FinRootZ` (`rgt#`, end `lft`) is imposed. -/
def ArcticBarrierBZrevf : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (J : DLetter → AffFun ArcZ d), FinRootZ hd J Letter.rgt Letter.lft →
    (∀ ρ ∈ usableSTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) →
    (∀ π ∈ pairsPDrev, WeakTop hd (evA J π.lhs) (evA J π.rhs)) →
    ∀ π ∈ pairsPDrev, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)

/-! ## Finiteness and lower bounds of values (from the weak premises) -/

/-- The symbols of the forward value string `bin'(n) rgt` are `f`, `t`, `rgt`. -/
lemma dw_fwd_letters (n : ℕ) :
    ∀ s ∈ binTail n ++ [Letter.rgt], s = Letter.f ∨ s = Letter.t ∨ s = Letter.rgt := by
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · rcases binTail_letters n s hs with rfl | rfl <;> simp
  · rw [List.mem_singleton] at hs; subst hs; simp

/-- The symbols of the reversed value string `rev(bin'(n)) lft` are `f`, `t`, `lft`. -/
lemma dw_rev_letters (n : ℕ) :
    ∀ s ∈ (binTail n).reverse ++ [Letter.lft], s = Letter.f ∨ s = Letter.t ∨ s = Letter.lft := by
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · rcases binTail_letters n s (List.mem_reverse.mp hs) with rfl | rfl <;> simp
  · rw [List.mem_singleton] at hs; subst hs; simp

/-- `𝔸_ℕ`: under the weak condition `SFRoot`, the value of a string of `f`, `t`, `e` only is finite (if the absolute part of `h#` is finite, then `V ≥ c_{h#}[1]`;
otherwise the argument of Koprowski–Waldmann 2009, Lemma 6.2, `Vw_ne_zero`). -/
lemma dw_Vw_ne_zero {d : ℕ} (hd : 0 < d) (J : DLetter → AffFun Arc d) (h e : Letter)
    (hSF : SFRoot hd J h e) (w : Word) (hw : ∀ s ∈ w, s = Letter.f ∨ s = Letter.t ∨ s = e) :
    Vw hd J h w ≠ 0 := by
  rcases hSF with hc | hSF
  · rw [Vw_eq_mulVec]
    refine Arc.ne_zero_of_le (hom_mulVec_ge_c hd _ _) ?_
    rw [yvec_last, mul_one]; exact hc
  · refine Vw_ne_zero hd J _ hSF h (by simp) w (fun s hs => ?_)
    rcases hw s hs with rfl | rfl | rfl <;> simp

/-- Below zero: under the weak condition `FinRootZ`, the values of nonempty strings of `f`, `t`, `e` only are uniformly bounded below. -/
lemma dw_Vw_lb {d : ℕ} (hd : 0 < d) (J : DLetter → AffFun ArcZ d) (h e : Letter)
    (hF : FinRootZ hd J h e) : ∃ C : ℤ, ∀ w : Word, w ≠ [] →
      (∀ s ∈ w, s = Letter.f ∨ s = Letter.t ∨ s = e) → ArcZ.fin C ≤ Vw hd J h w := by
  rcases hF with hc | ⟨hM, hcs⟩
  · -- `V ≥ c_{h#}[1]`
    obtain ⟨C, hC⟩ := ArcZ.exists_fin_of_ne_zero hc
    refine ⟨C, fun w _ _ => ?_⟩
    have := hom_mulVec_ge_c hd (J (DLetter.mark h)) (evR (homL J) w *ᵥ xs hd)
    rw [yvec_last, mul_one, ← Vw_eq_mulVec, hC] at this
    exact this
  · -- `V ≥ M_{h#}[1,1] ⊗ c_s[1]` (`s` is the first symbol)
    obtain ⟨a, ha⟩ := ArcZ.exists_fin_of_ne_zero hM
    obtain ⟨bf, hbf⟩ := ArcZ.exists_fin_of_ne_zero (hcs Letter.f (by simp))
    obtain ⟨bt, hbt⟩ := ArcZ.exists_fin_of_ne_zero (hcs Letter.t (by simp))
    obtain ⟨be, hbe⟩ := ArcZ.exists_fin_of_ne_zero (hcs e (by simp))
    refine ⟨a + min bf (min bt be), fun w hw0 hw => ?_⟩
    obtain ⟨s, w', rfl⟩ := List.exists_cons_of_ne_nil hw0
    have hs : ∃ b : ℤ, (J (DLetter.plain s)).c ⟨0, hd⟩ = ArcZ.fin b ∧ min bf (min bt be) ≤ b := by
      rcases hw s List.mem_cons_self with rfl | rfl | rfl
      · exact ⟨bf, hbf, min_le_left _ _⟩
      · exact ⟨bt, hbt, (min_le_right _ _).trans (min_le_left _ _)⟩
      · exact ⟨be, hbe, (min_le_right _ _).trans (min_le_right _ _)⟩
    obtain ⟨b, hb, hbmin⟩ := hs
    have h1 := hom_mulVec_ge_M hd (J (DLetter.mark h)) (evR (homL J) (s :: w') *ᵥ xs hd)
    rw [← Vw_eq_mulVec] at h1
    have h2 : (J (DLetter.plain s)).c ⟨0, hd⟩ ≤ (evR (homL J) (s :: w') *ᵥ xs hd) (c0 hd) := by
      rw [evR_cons, ← Matrix.mulVec_mulVec]
      have := hom_mulVec_ge_c hd (J (DLetter.plain s)) (evR (homL J) w' *ᵥ xs hd)
      rw [yvec_last, mul_one] at this
      exact this
    calc ArcZ.fin (a + min bf (min bt be)) ≤ ArcZ.fin (a + b) :=
          ArcZ.fin_le_fin.mpr (by linarith)
      _ = (J (DLetter.mark h)).M ⟨0, hd⟩ ⟨0, hd⟩ * (J (DLetter.plain s)).c ⟨0, hd⟩ := by
          rw [ha, hb, ArcZ.fin_mul_fin]
      _ ≤ (J (DLetter.mark h)).M ⟨0, hd⟩ ⟨0, hd⟩ * (evR (homL J) (s :: w') *ᵥ xs hd) (c0 hd) :=
          ArcticOrder.mul_mono le_rfl h2
      _ ≤ Vw hd J h (s :: w') := h1

/-! ## Translation below zero (from a lower bound) -/

lemma dw_autoValZ_smul {D : ℕ} (a : ArcZ) (u : Fin D → ArcZ)
    (A : Letter → Matrix (Fin D) (Fin D) ArcZ) (c : Fin D → ArcZ) (n : ℕ) :
    autoValZ (a • u) A c n = a * autoValZ u A c n := by
  unfold autoValZ
  rw [smul_dotProduct, smul_eq_mul]

/-- **Translation (from a lower bound)**: if the values of an automaton over `ℤ ∪ {−∞}` are uniformly at least `C` and decrease in each `T`-step by the number
of uses of a strictly oriented rule, this contradicts `AutoCore` (translate `u` by `−C` and apply `BZShift.barrier_of_auto_arcZ`). -/
theorem dw_barrier_of_lb (hcore : AutoCore) {D : ℕ} (u : Fin D → ArcZ)
    (A : Letter → Matrix (Fin D) (Fin D) ArcZ) (c : Fin D → ArcZ) (σ : Rule) (hσ : σ ∈ rulesST)
    (C : ℤ) (hlb : ∀ n, ArcZ.fin C ≤ autoValZ u A c n)
    (hstep : ∀ n, 2 ≤ n → autoValZ u A c (T n) * ArcZ.fin 1 ^ (uses σ n) ≤ autoValZ u A c n) :
    False := by
  refine barrier_of_auto_arcZ hcore (ArcZ.fin (-C) • u) A c σ hσ ?_ ?_
  · intro n
    rw [dw_autoValZ_smul]
    have h := hlb n
    have hne : autoValZ u A c n ≠ 0 := by
      intro h0; rw [h0, ArcZ.le_iff_val] at h; simp at h
    obtain ⟨z, hz⟩ := ArcZ.exists_fin_of_ne_zero hne
    rw [hz, ArcZ.fin_le_fin] at h
    rw [hz, ArcZ.fin_mul_fin]
    exact ⟨(-C + z).toNat, by rw [Int.toNat_of_nonneg (by omega)]⟩
  · intro n hn
    rw [dw_autoValZ_smul, dw_autoValZ_smul, mul_assoc]
    exact ArcticOrder.mul_mono le_rfl (hstep n hn)

/-! ## Core lemmas (with finiteness or lower bounds of values as hypotheses) -/

/-- Forward (`𝔸_ℕ`): the barrier with finiteness of values as a hypothesis `hfin`, in a form derivable from the estimate for `T`-steps. -/
theorem dw_DP_core (hcore : AutoCore) {d : ℕ} (hd : 0 < d) (J : DLetter → AffFun Arc d)
    (hU : ∀ ρ ∈ usableST, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs))
    (hP : ∀ π ∈ pairsPB, WeakTop hd (evA J π.lhs) (evA J π.rhs))
    (hfin : (∀ n, 2 ≤ n → ∃ k, Vw hd J Letter.lft (binTail (T n) ++ [Letter.rgt]) * Arc.fin 1 ^ k ≤
        Vw hd J Letter.lft (binTail n ++ [Letter.rgt])) →
      ∀ n, Vw hd J Letter.lft (binTail n ++ [Letter.rgt]) ≠ 0) :
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
  have hstep : ∀ n, 2 ≤ n → Vw hd J Letter.lft (binTail (T n) ++ [Letter.rgt]) *
      Arc.fin 1 ^ (uses σ n) ≤ Vw hd J Letter.lft (binTail n ++ [Letter.rgt]) := fun n hn =>
    Vw_chain hd J Letter.lft (Arc.fin 1) (fun _ _ h => Arc.gg_mul_fin_one h) hU hPw hσU hs
      (dcanDeriv n hn)
  have hf := hfin (fun n hn => ⟨_, hstep n hn⟩)
  refine barrier_of_auto_arc hcore (fun j => hom (J (DLetter.mark Letter.lft)) (c0 hd) j) (homL J)
    (homL J Letter.rgt *ᵥ xs hd) σ hσST ?_ ?_
  · intro n
    have := hf n
    rwa [Vw_fwd_eq] at this
  · intro n hn
    have := hstep n hn
    rwa [Vw_fwd_eq, Vw_fwd_eq] at this

/-- Reversed (`𝔸_ℕ`): the same. -/
theorem dw_DPrev_core (hcore : AutoCore) {d : ℕ} (hd : 0 < d) (J : DLetter → AffFun Arc d)
    (hU : ∀ ρ ∈ usableSTrev, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs))
    (hP : ∀ π ∈ pairsPDrev, WeakTop hd (evA J π.lhs) (evA J π.rhs))
    (hfin : (∀ n, 2 ≤ n → ∃ k, Vw hd J Letter.rgt ((binTail (T n)).reverse ++ [Letter.lft]) *
        Arc.fin 1 ^ k ≤ Vw hd J Letter.rgt ((binTail n).reverse ++ [Letter.lft])) →
      ∀ n, Vw hd J Letter.rgt ((binTail n).reverse ++ [Letter.lft]) ≠ 0) :
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
  have hstep : ∀ n, 2 ≤ n → Vw hd J Letter.rgt ((binTail (T n)).reverse ++ [Letter.lft]) *
      Arc.fin 1 ^ (uses τ n) ≤ Vw hd J Letter.rgt ((binTail n).reverse ++ [Letter.lft]) := by
    intro n hn
    have := Vw_chain hd J Letter.rgt (Arc.fin 1) (fun _ _ h => Arc.gg_mul_fin_one h) hU hPw hσU hs
      (dcanDeriv_rev n hn)
    rwa [count_rev] at this
  have hf := hfin (fun n hn => ⟨_, hstep n hn⟩)
  refine barrier_of_auto_arc hcore (homL J Letter.lft *ᵥ xs hd) (fun s => (homL J s)ᵀ)
    (fun j => hom (J (DLetter.mark Letter.rgt)) (c0 hd) j) τ hτ ?_ ?_
  · intro n
    have := hf n
    rwa [Vw_rev_eq] at this
  · intro n hn
    have := hstep n hn
    rwa [Vw_rev_eq, Vw_rev_eq] at this

end Collatz.Arctic
