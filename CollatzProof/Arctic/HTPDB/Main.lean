/-
The bridge for the system $\mathcal H$: the five main theorems from the intermediate statement `AutoCoreH`
(the case $\mathcal H$ of Theorems 3.1, 3.3 and 3.4).

* `barrierHT_of_auto : AutoCoreH → ArcticBarrierHT` (rule removal): `Gen.barrier_of_autoCoreG` applied to the correctness of the canonical derivations,
  `canDerivH_chain`, and the membership of their rules, `canDerivH_sub` (adapted from `Main.arctic_barrier_ST` and
  `AutoBridge.valueCore_of_autoCore`).
* `barrierHDP_of_auto`, `barrierHDPrev_of_auto` (dependency pairs, `𝔸_ℕ`, forward and reversed): the value `V(n)` is the value of an automaton in homogeneous coordinates
  (transposed in the reversed case). It is finite by somewhere finiteness, does not increase under a step of `Hmap` (at points of `HDom`), and decreases by the number of uses of the strictly oriented pair
  (the canonical dependency pair chains `dcanDerivH`, `dcanDerivH_rev`). `Gen.barrier_of_auto_arcG` gives a contradiction (adapted from
  `DPMain.arctic_barrier_DP`, `arctic_barrier_DPrev`).
* `barrierHBZ_of_auto`, `barrierHBZrev_of_auto` (below zero, `𝔸_ℤ`, forward and reversed): by absolute positivity the value is a natural number
  (`BZMain.Vw_nat`). Finally the translation, `Gen.barrier_of_auto_arcZG` (adapted from `BZMain.arctic_barrier_BZ`,
  `arctic_barrier_BZrev`).
* `specBridgeH : SpecBridgeH` (the frozen interface statement of `HTPDB/Spec.lean`).
-/
import CollatzProof.Arctic.HTPDB.Canon
import CollatzProof.Arctic.HTPDB.DPCanon
import CollatzProof.Arctic.HTPDB.Spec

namespace Collatz.Arctic.HTPDB

open Collatz.Arctic HModel Matrix

/-- **Theorem 3.1 ($\mathcal H$, rule removal) from `AutoCoreH`**. -/
theorem barrierHT_of_auto (h : AutoCoreH) : ArcticBarrierHT :=
  Gen.barrier_of_autoCoreG h canDerivH_chain (fun n _ => canDerivH_sub n)

/-- The root rules of `P_B` do not belong to `usableHT` and belong to `rulesHT`. -/
private lemma rootPB_props {σ : Rule} (hσ : σ ∈ rootPB) : σ ∉ usableHT ∧ σ ∈ rulesHT := by
  simp only [rootPB, List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl <;> decide

/-- The letters of `bin'(n) .` belong to `lettersPB`. -/
private lemma fwd_letters (n : ℕ) :
    ∀ s ∈ binTail n ++ [Letter.rgt], DLetter.plain s ∈ lettersPB := by
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · rcases binTail_letters n s hs with rfl | rfl <;> decide
  · rw [List.mem_singleton] at hs; subst hs; decide

/-- The letters of `rev(bin'(n)) /` belong to `lettersPDrev`. -/
private lemma rev_letters (n : ℕ) :
    ∀ s ∈ (binTail n).reverse ++ [Letter.lft], DLetter.plain s ∈ lettersPDrev := by
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · rcases binTail_letters n s (List.mem_reverse.mp hs) with rfl | rfl <;> decide
  · rw [List.mem_singleton] at hs; subst hs; decide

/-- **Theorem 3.3 ($\mathcal H$, forward, `𝔸_ℕ`) from `AutoCoreH`**. -/
theorem barrierHDP_of_auto (hcore : AutoCoreH) : ArcticBarrierHDP := by
  intro d hd J hSF hU hP π hπ hs
  rw [pairsPB_eq] at hπ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hπ
  have hPw : ∀ ρ ∈ rootPB, WeakTop hd (evA J (dp Letter.lft ρ).lhs) (evA J (dp Letter.lft ρ).rhs) :=
    fun ρ hρ => hP _ (by rw [pairsPB_eq]; exact List.mem_map_of_mem hρ)
  obtain ⟨hσU, hσH⟩ := rootPB_props hσ
  refine Gen.barrier_of_auto_arcG hcore (fun j => hom (J (DLetter.mark Letter.lft)) (c0 hd) j)
    (homL J) (homL J Letter.rgt *ᵥ xs hd) σ hσH ?_ ?_
  · intro n
    have := Vw_ne_zero hd J lettersPB hSF Letter.lft (by decide) (binTail n ++ [Letter.rgt])
      (fwd_letters n)
    rwa [Vw_fwd_eq] at this
  · intro n hn
    have := Vw_chain hd J Letter.lft (Arc.fin 1) (fun _ _ h => Arc.gg_mul_fin_one h) hU hPw hσU hs
      (dcanDerivH n hn)
    rwa [Vw_fwd_eq, Vw_fwd_eq] at this

/-- **Theorem 3.3 ($\mathcal H$, reversed, `𝔸_ℕ`) from `AutoCoreH`**. -/
theorem barrierHDPrev_of_auto (hcore : AutoCoreH) : ArcticBarrierHDPrev := by
  intro d hd J hSF hU hP π hπ hs
  rw [pairsPDrevH_eq] at hπ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hπ
  have hPw : ∀ ρ ∈ rootPDrevH,
      WeakTop hd (evA J (dp Letter.rgt ρ).lhs) (evA J (dp Letter.rgt ρ).rhs) :=
    fun ρ hρ => hP _ (by rw [pairsPDrevH_eq]; exact List.mem_map_of_mem hρ)
  have hσU : σ ∉ usableHTrev := by
    simp only [rootPDrevH, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl <;> decide
  obtain ⟨τ, hτ, rfl⟩ := rootPDrevH_mem hσ
  refine Gen.barrier_of_auto_arcG hcore (homL J Letter.lft *ᵥ xs hd) (fun s => (homL J s)ᵀ)
    (fun j => hom (J (DLetter.mark Letter.rgt)) (c0 hd) j) τ hτ ?_ ?_
  · intro n
    have := Vw_ne_zero hd J lettersPDrev hSF Letter.rgt (by decide)
      ((binTail n).reverse ++ [Letter.lft]) (rev_letters n)
    rwa [Vw_rev_eq] at this
  · intro n hn
    have := Vw_chain hd J Letter.rgt (Arc.fin 1) (fun _ _ h => Arc.gg_mul_fin_one h) hU hPw hσU hs
      (dcanDerivH_rev n hn)
    rwa [Vw_rev_eq, Vw_rev_eq, count_revH] at this

/-- **Theorem 3.4 ($\mathcal H$, forward, below zero `𝔸_ℤ`) from `AutoCoreH`**. -/
theorem barrierHBZ_of_auto (hcore : AutoCoreH) : ArcticBarrierHBZ := by
  intro d hd J hAP hU hP π hπ hs
  rw [pairsPB_eq] at hπ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hπ
  have hPw : ∀ ρ ∈ rootPB, WeakTop hd (evA J (dp Letter.lft ρ).lhs) (evA J (dp Letter.lft ρ).rhs) :=
    fun ρ hρ => hP _ (by rw [pairsPB_eq]; exact List.mem_map_of_mem hρ)
  obtain ⟨hσU, hσH⟩ := rootPB_props hσ
  refine Gen.barrier_of_auto_arcZG hcore (fun j => hom (J (DLetter.mark Letter.lft)) (c0 hd) j)
    (homL J) (homL J Letter.rgt *ᵥ xs hd) σ hσH ?_ ?_
  · intro n
    obtain ⟨z, hz⟩ := Vw_nat hd J Letter.lft (hAP _ (by decide)) (binTail n ++ [Letter.rgt])
    exact ⟨z, by rw [autoValZ, ← Vw_fwd_eq]; exact hz⟩
  · intro n hn
    have := Vw_chain hd J Letter.lft (ArcZ.fin 1) (fun _ _ h => ArcZ.gg_mul_fin_one h) hU hPw hσU
      hs (dcanDerivH n hn)
    rwa [Vw_fwd_eq, Vw_fwd_eq] at this

/-- **Theorem 3.4 ($\mathcal H$, reversed, below zero `𝔸_ℤ`) from `AutoCoreH`**. -/
theorem barrierHBZrev_of_auto (hcore : AutoCoreH) : ArcticBarrierHBZrev := by
  intro d hd J hAP hU hP π hπ hs
  rw [pairsPDrevH_eq] at hπ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hπ
  have hPw : ∀ ρ ∈ rootPDrevH,
      WeakTop hd (evA J (dp Letter.rgt ρ).lhs) (evA J (dp Letter.rgt ρ).rhs) :=
    fun ρ hρ => hP _ (by rw [pairsPDrevH_eq]; exact List.mem_map_of_mem hρ)
  have hσU : σ ∉ usableHTrev := by
    simp only [rootPDrevH, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl <;> decide
  obtain ⟨τ, hτ, rfl⟩ := rootPDrevH_mem hσ
  refine Gen.barrier_of_auto_arcZG hcore (homL J Letter.lft *ᵥ xs hd) (fun s => (homL J s)ᵀ)
    (fun j => hom (J (DLetter.mark Letter.rgt)) (c0 hd) j) τ hτ ?_ ?_
  · intro n
    obtain ⟨z, hz⟩ := Vw_nat hd J Letter.rgt (hAP _ (by decide))
      ((binTail n).reverse ++ [Letter.lft])
    exact ⟨z, by rw [autoValZ, ← Vw_rev_eq]; exact hz⟩
  · intro n hn
    have := Vw_chain hd J Letter.rgt (ArcZ.fin 1) (fun _ _ h => ArcZ.gg_mul_fin_one h) hU hPw hσU
      hs (dcanDerivH_rev n hn)
    rwa [Vw_rev_eq, Vw_rev_eq, count_revH] at this

/-- **Output of the bridge** (the frozen interface statement `SpecBridgeH`): the five main theorems from `AutoCoreH`. -/
theorem specBridgeH : SpecBridgeH := fun h =>
  ⟨barrierHT_of_auto h, barrierHDP_of_auto h, barrierHDPrev_of_auto h, barrierHBZ_of_auto h,
    barrierHBZrev_of_auto h⟩

end Collatz.Arctic.HTPDB
