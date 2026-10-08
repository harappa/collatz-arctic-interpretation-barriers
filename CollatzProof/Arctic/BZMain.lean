/-
The arctic barrier in dependency pair form below zero (`𝔸_ℤ`; Theorem 3.4 of the paper).

* `arctic_barrier_BZ : AutoCore → ArcticBarrierBZ` (for 𝒯),
  `arctic_barrier_BZrev : AutoCore → ArcticBarrierBZrev` (for the reversal).
* Proof: by absolute positivity the values are at least `c_{h#}[1] ≥ 0`, hence natural numbers (Koprowski–Waldmann 2009, Lemma 8.2; `Vw_nat`). The canonical chains and
  `Vw_chain` are shared with `𝔸_ℕ`; at the end the translation (`BZShift.barrier_of_auto_arcZ`; Lemma 5.3) applies `AutoCore`.
-/
import CollatzProof.Arctic.BZShift

namespace Collatz.Arctic

open Matrix

/-- With absolute positivity (`𝔸_ℤ`) the values are natural numbers (Koprowski–Waldmann 2009, Lemma 8.2: `V ≥ c_{h#}[1] ≥ 0`). -/
lemma Vw_nat {d : ℕ} (hd : 0 < d) (J : DLetter → AffFun ArcZ d) (h : Letter)
    (hpos : ArcZ.fin 0 ≤ (J (DLetter.mark h)).c ⟨0, hd⟩) (w : Word) :
    ∃ z : ℕ, Vw hd J h w = ArcZ.fin z := by
  have := hom_mulVec_ge_c hd (J (DLetter.mark h)) (evR (homL J) w *ᵥ xs hd)
  rw [yvec_last, mul_one, ← Vw_eq_mulVec] at this
  exact ArcZ.exists_nat_of_le (hpos.trans this)

/-- **Theorem 3.4 (𝒯, below zero `𝔸_ℤ`)**. -/
theorem arctic_barrier_BZ (hcore : AutoCore) : ArcticBarrierBZ := by
  intro d hd J hAP hU hP π hπ hs
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
  refine barrier_of_auto_arcZ hcore (fun j => hom (J (DLetter.mark Letter.lft)) (c0 hd) j)
    (homL J) (homL J Letter.rgt *ᵥ xs hd) σ hσST ?_ ?_
  · intro n
    obtain ⟨z, hz⟩ := Vw_nat hd J Letter.lft (hAP _ (by decide)) (binTail n ++ [Letter.rgt])
    exact ⟨z, by rw [autoValZ, ← Vw_fwd_eq]; exact hz⟩
  · intro n hn
    have := Vw_chain hd J Letter.lft (ArcZ.fin 1) (fun _ _ h => ArcZ.gg_mul_fin_one h) hU hPw hσU
      hs (dcanDeriv n hn)
    rwa [Vw_fwd_eq, Vw_fwd_eq] at this

/-- **Theorem 3.4 (the reversal of 𝒯, below zero `𝔸_ℤ`)**. -/
theorem arctic_barrier_BZrev (hcore : AutoCore) : ArcticBarrierBZrev := by
  intro d hd J hAP hU hP π hπ hs
  rw [pairsPDrev_eq] at hπ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hπ
  have hPw : ∀ ρ ∈ rootPDrev,
      WeakTop hd (evA J (dp Letter.rgt ρ).lhs) (evA J (dp Letter.rgt ρ).rhs) :=
    fun ρ hρ => hP _ (by rw [pairsPDrev_eq]; exact List.mem_map_of_mem hρ)
  have hσU : σ ∉ usableSTrev := by
    simp only [rootPDrev, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl <;> decide
  obtain ⟨τ, hτ, rfl⟩ := rootPDrev_mem hσ
  refine barrier_of_auto_arcZ hcore (homL J Letter.lft *ᵥ xs hd) (fun s => (homL J s)ᵀ)
    (fun j => hom (J (DLetter.mark Letter.rgt)) (c0 hd) j) τ hτ ?_ ?_
  · intro n
    obtain ⟨z, hz⟩ := Vw_nat hd J Letter.rgt (hAP _ (by decide))
      ((binTail n).reverse ++ [Letter.lft])
    exact ⟨z, by rw [autoValZ, ← Vw_rev_eq]; exact hz⟩
  · intro n hn
    have := Vw_chain hd J Letter.rgt (ArcZ.fin 1) (fun _ _ h => ArcZ.gg_mul_fin_one h) hU hPw hσU
      hs (dcanDeriv_rev n hn)
    rwa [Vw_rev_eq, Vw_rev_eq, count_rev] at this

end Collatz.Arctic
