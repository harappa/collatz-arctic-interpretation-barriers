/-
The arctic barrier in dependency pair form (`𝔸_ℕ`; Theorem 3.3 of the paper).

* `arctic_barrier_DP : AutoCore → ArcticBarrierDP` (for 𝒯; `P_B` and `𝒰 = D_T ∪ A`).
* `arctic_barrier_DPrev : AutoCore → ArcticBarrierDPrev` (for the reversal; `P_D^rev` and `A^rev ∪ B^rev`).
* Proof: the value `V(n)` is the value of an automaton in homogeneous coordinates (for the reversal, after transposition). It is finite by somewhere finiteness (Koprowski–Waldmann 2009, Lemma 6.2;
  `yvec_ne_zero`), does not increase along steps of `T`, and decreases by the number of uses of a strictly oriented dependency pair. Applying `AutoCore` with `κ = 0`
  gives a contradiction as in `Main.arctic_barrier_ST` (`barrier_of_auto_arc`).
-/
import CollatzProof.Arctic.DPCanon
import CollatzProof.Arctic.AutoStatement

namespace Collatz.Arctic

open Matrix Arc

/-- With somewhere finiteness (`𝔸_ℕ`), the first component of the value vector is finite (Koprowski–Waldmann 2009, Lemma 6.2). -/
lemma yvec_ne_zero {d : ℕ} (hd : 0 < d) (J : DLetter → AffFun Arc d) (S : List DLetter)
    (hSF : SomewhereFinite hd J S) :
    ∀ w : Word, (∀ s ∈ w, DLetter.plain s ∈ S) → (evR (homL J) w *ᵥ xs hd) (c0 hd) ≠ 0 := by
  intro w
  induction w with
  | nil =>
    intro _
    simp only [evR_nil, Matrix.one_mulVec, xs, c0, Fin.lastCases_castSucc, ↓reduceIte]
    rw [ne_zero_iff]; simp
  | cons s w ih =>
    intro hw
    have hrest := ih (fun s' hs' => hw s' (List.mem_cons_of_mem _ hs'))
    rw [evR_cons, ← Matrix.mulVec_mulVec]
    rcases hSF _ (hw s List.mem_cons_self) with hc | hM
    · refine ne_zero_of_le (hom_mulVec_ge_c hd _ _) ?_
      rw [yvec_last, mul_one]; exact hc
    · exact ne_zero_of_le (hom_mulVec_ge_M hd _ _) (mul_ne_zero' hM hrest)

/-- With somewhere finiteness (`𝔸_ℕ`), the value is finite. -/
lemma Vw_ne_zero {d : ℕ} (hd : 0 < d) (J : DLetter → AffFun Arc d) (S : List DLetter)
    (hSF : SomewhereFinite hd J S) (h : Letter) (hh : DLetter.mark h ∈ S)
    (w : Word) (hw : ∀ s ∈ w, DLetter.plain s ∈ S) : Vw hd J h w ≠ 0 := by
  rw [Vw_eq_mulVec]
  rcases hSF _ hh with hc | hM
  · refine ne_zero_of_le (hom_mulVec_ge_c hd _ _) ?_
    rw [yvec_last, mul_one]; exact hc
  · exact ne_zero_of_le (hom_mulVec_ge_M hd _ _) (mul_ne_zero' hM (yvec_ne_zero hd J S hSF w hw))

/-- The value barrier over `𝔸_ℕ`: the estimate along steps of `T` and finiteness contradict `AutoCore` (`κ = 0`). -/
lemma barrier_of_auto_arc (hcore : AutoCore) {D : ℕ} (u : Fin D → Arc) (A : Interp D)
    (c : Fin D → Arc) (σ : Rule) (hσ : σ ∈ rulesST)
    (hfin : ∀ n, autoVal u A c n ≠ 0)
    (hstep : ∀ n, 2 ≤ n → autoVal u A c (T n) * fin 1 ^ (uses σ n) ≤ autoVal u A c n) :
    False := by
  have horb := orbit_chain (fun n => autoVal u A c n) (fin 1) σ hstep
  obtain ⟨n, -, m, hm, hlt⟩ := hcore D u A c 0 (fun n _ => hfin n)
    (by
      intro n hn a b ha hb
      have := hstep n hn
      rw [ha, hb, fin_one_pow, fin_mul_fin, fin_le_fin] at this
      omega)
    σ hσ 0
  -- contradiction between the conclusion `V(n) < number of uses` and the estimate `V(T^m n) + number of uses ≤ V(n)` along the orbit
  obtain ⟨a, ha⟩ := exists_fin_of_ne_zero (hfin n)
  obtain ⟨b, hb⟩ := exists_fin_of_ne_zero (hfin (T^[m] n))
  have := horb m n hm
  rw [ha, hb, fin_one_pow, fin_mul_fin, fin_le_fin] at this
  rw [ha, zero_mul, zero_add, fin_lt_fin] at hlt
  omega

/-- **Theorem 3.3 (𝒯, `𝔸_ℕ`)**. -/
theorem arctic_barrier_DP (hcore : AutoCore) : ArcticBarrierDP := by
  intro d hd J hSF hU hP π hπ hs
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
  refine barrier_of_auto_arc hcore (fun j => hom (J (DLetter.mark Letter.lft)) (c0 hd) j) (homL J)
    (homL J Letter.rgt *ᵥ xs hd) σ hσST ?_ ?_
  · intro n
    have := Vw_ne_zero hd J lettersPB hSF Letter.lft (by decide) (binTail n ++ [Letter.rgt])
      (by
        intro s hs
        rcases List.mem_append.mp hs with hs | hs
        · rcases binTail_letters n s hs with rfl | rfl <;> decide
        · rw [List.mem_singleton] at hs; subst hs; decide)
    rwa [Vw_fwd_eq] at this
  · intro n hn
    have := Vw_chain hd J Letter.lft (fin 1) (fun _ _ h => gg_mul_fin_one h) hU hPw hσU hs
      (dcanDeriv n hn)
    rwa [Vw_fwd_eq, Vw_fwd_eq] at this

/-- **Theorem 3.3 (the reversal of 𝒯, `𝔸_ℕ`)**. -/
theorem arctic_barrier_DPrev (hcore : AutoCore) : ArcticBarrierDPrev := by
  intro d hd J hSF hU hP π hπ hs
  rw [pairsPDrev_eq] at hπ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hπ
  have hPw : ∀ ρ ∈ rootPDrev,
      WeakTop hd (evA J (dp Letter.rgt ρ).lhs) (evA J (dp Letter.rgt ρ).rhs) :=
    fun ρ hρ => hP _ (by rw [pairsPDrev_eq]; exact List.mem_map_of_mem hρ)
  have hσU : σ ∉ usableSTrev := by
    simp only [rootPDrev, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl <;> decide
  obtain ⟨τ, hτ, rfl⟩ := rootPDrev_mem hσ
  refine barrier_of_auto_arc hcore (homL J Letter.lft *ᵥ xs hd) (fun s => (homL J s)ᵀ)
    (fun j => hom (J (DLetter.mark Letter.rgt)) (c0 hd) j) τ hτ ?_ ?_
  · intro n
    have := Vw_ne_zero hd J lettersPDrev hSF Letter.rgt (by decide)
      ((binTail n).reverse ++ [Letter.lft])
      (by
        intro s hs
        rcases List.mem_append.mp hs with hs | hs
        · rcases binTail_letters n s (List.mem_reverse.mp hs) with rfl | rfl <;> decide
        · rw [List.mem_singleton] at hs; subst hs; decide)
    rwa [Vw_rev_eq] at this
  · intro n hn
    have := Vw_chain hd J Letter.rgt (fin 1) (fun _ _ h => gg_mul_fin_one h) hU hPw hσU hs
      (dcanDeriv_rev n hn)
    rwa [Vw_rev_eq, Vw_rev_eq, count_rev] at this

end Collatz.Arctic
