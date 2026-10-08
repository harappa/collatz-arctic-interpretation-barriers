/-
# Theorem 11.8 on the restriction to the relevant indices, and passing it to Lemma 11.3

The main theorem `lyap_compare` of `H2Lyap.lean` (hypothesis `hall`: every index is relevant) is put in a form that applies to the restriction
`restrictRel A` of a general automaton `A` to its relevant indices (the restriction $\mathcal N^{\mathrm{rel}}$ of Definition 10.1, the automaton on `Q'`).
This is the entry to Proposition 11.13 (`hT` and `h3` are transferred to `L' := restrictRel L` by `aval_restrictRel`),
together with `rel_restrictRel` (every index of the restriction is relevant).

* `rel_restrictRel`: after the restriction, every index is relevant.
* `lyap_compare_restrict`: if the values of `A` satisfy `hT` and `h3`, then `restrictRel A` satisfies `∀ κ ≥ 1, κ log G' ≤ bAvg'_κ`
  (`G' := gDiag (restrictRel A).B`).
* `lyap_compare_gen`: the form for the restriction of the lift `liftT (genAuto N a z)` of a general family `N` that weakly orients the 11 rules of $\mathcal T$ entrywise
  (including the homogeneous matrices of natural-number matrix interpretations).
* `top_rigid_of_T_mono`, `top_heavy_of_T_mono`: the hypothesis `hLC` of `top_rigid` and `top_heavy` (Lemma 11.3, Corollary 11.4) filled in by `lyap_compare`
  (if `1 < G'`, there are a component rigid at `G'` and a heavy family of words). A check that the output of Theorem 11.8 fits the input of Lemma 11.3 as it is.

Auxiliary declarations are in the namespace `Collatz.Arctic.NatQ5.W2c`, the main theorems in `Collatz.Arctic.NatQ5`.
`sorry`, `axiom` and `native_decide` are not used.
-/
import CollatzProof.Arctic.Nat.H2Lyap
import CollatzProof.Arctic.Nat.H2Top

namespace Collatz.Arctic.NatQ5.W2c

open Collatz.Arctic Collatz.Arctic.NatQ5 Matrix

set_option linter.unusedSectionVars false

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-! ## §1 Paths on the restriction -/

/-- The entries of the product of a word on the restriction are entries of the original product (the set of relevant indices is path-closed). -/
theorem DxN_restrictRel_apply (A : ValAuto Q) (w : List (Fin 2)) (x y : relSet A) :
    Rigid.DxN (restrictRel A).B w x y = Rigid.DxN A.B w x.1 y.1 := by
  show Rigid.DxN (restrictB A (relSet A)) w x y = _
  rw [DxN_restrict A (relSet_convex A) w]
  rfl

/-- A path of the original automaton whose end points are relevant is a path on the restriction. -/
theorem conn_restrictRel {A : ValAuto Q} {x y : relSet A} (h : Conn A x.1 y.1) : Conn (restrictRel A) x y := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, by rw [DxN_restrictRel_apply]; exact hw⟩

/-- After the restriction to the relevant indices, every index is relevant. -/
theorem rel_restrictRel (A : ValAuto Q) : ∀ x : relSet A, Rel (restrictRel A) x := by
  intro x
  have hx : Rel A x.1 := (mem_relSet A).1 x.2
  obtain ⟨⟨i, hi, hix⟩, ⟨j, hxj, hj⟩⟩ := hx
  have hiR : Rel A i := ⟨⟨i, hi, conn_refl A i⟩, ⟨j, conn_trans A hix hxj, hj⟩⟩
  have hjR : Rel A j := ⟨⟨i, hi, conn_trans A hix hxj⟩, ⟨j, conn_refl A j, hj⟩⟩
  refine ⟨⟨⟨i, (mem_relSet A).2 hiR⟩, hi, conn_restrictRel hix⟩, ⟨⟨j, (mem_relSet A).2 hjR⟩, conn_restrictRel hxj, hj⟩⟩

end Collatz.Arctic.NatQ5.W2c

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic W2c

set_option linter.unusedSectionVars false

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-! ## §2 The restricted version and passing to Lemma 11.3 -/

/-- **The restricted version of Theorem 11.8**: if the values of `A` do not increase along steps of `T` from numbers `n ≥ 2` not divisible by 3 and vanish on multiples of 3, then the restriction
`restrictRel A` to the relevant indices satisfies `∀ κ ≥ 1, κ log G' ≤ bAvg'_κ` (`G' := gDiag (restrictRel A).B`). -/
theorem lyap_compare_restrict (A : ValAuto Q)
    (hT : ∀ n, 2 ≤ n → ¬ 3 ∣ n → aval A (binWord (Collatz.Arctic.T n)) ≤ aval A (binWord n))
    (h3 : ∀ n, 1 ≤ n → 3 ∣ n → aval A (binWord n) = 0) :
    ∀ κ : ℕ, 1 ≤ κ → (κ : ℝ) * Real.log (Rigid.gDiag (restrictRel A).B) ≤ Rigid.bAvg (restrictRel A).B κ :=
  lyap_compare (restrictRel A) (rel_restrictRel A)
    (fun n hn hn3 => by rw [aval_restrictRel, aval_restrictRel]; exact hT n hn hn3)
    (fun n hn hn3 => by rw [aval_restrictRel]; exact h3 n hn hn3)

/-- **Application to general families that weakly orient $\mathcal T$** (the entry to `h2_gen`, Corollary 10.9 (2)): if `N` weakly orients all 11 rules
entrywise, then the restriction of the lift `liftT (genAuto N a z)` to its relevant indices (the automaton on `Q'`) satisfies
`∀ κ ≥ 1, κ log G' ≤ bAvg'_κ`. `hT` is `gavalT_T_le`, the lifted version of Lemma 10.2, and `h3` is the value identity `aval_liftT`. -/
theorem lyap_compare_gen {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Letter → Matrix ι ι ℕ) (a z : ι)
    (hw : ∀ ρ ∈ rulesST, GWeak N ρ) :
    ∀ κ : ℕ, 1 ≤ κ → (κ : ℝ) * Real.log (Rigid.gDiag (restrictRel (liftT (genAuto N a z))).B) ≤
      Rigid.bAvg (restrictRel (liftT (genAuto N a z))).B κ :=
  lyap_compare_restrict (liftT (genAuto N a z)) (fun n hn hn3 => gavalT_T_le hw a z hn hn3)
    (fun n hn hn3 => by rw [aval_liftT _ n hn]; simp [hn3])

/-- **Passing to Lemma 11.3**: the hypothesis `hdiag` of `top_rigid` filled in by `diag_le_gDiag`, and `hLC` by `lyap_compare`.
If `G := gDiag L.B > 1`, there is a strongly connected component rigid at `G`. -/
theorem top_rigid_of_T_mono (L : ValAuto Q) (hall : ∀ q, Rel L q)
    (hT : ∀ n, 2 ≤ n → ¬ 3 ∣ n → aval L (binWord (Collatz.Arctic.T n)) ≤ aval L (binWord n))
    (h3 : ∀ n, 1 ≤ n → 3 ∣ n → aval L (binWord n) = 0) (hG : 1 < Rigid.gDiag L.B) :
    ∃ q, Rigid.RigidAt (compMat L (sccOf L q)) (Rigid.gDiag L.B) :=
  top_rigid L hG (Rigid.diag_le_gDiag L.B) (lyap_compare L hall hT h3)

/-- The form applied to `top_heavy` (Corollary 11.4; the heavy family `(B_{ω_ε})_{aa} ≥ c G^{|ω_ε|}`). The entry to Proposition 11.13. -/
theorem top_heavy_of_T_mono (L : ValAuto Q) (hall : ∀ q, Rel L q)
    (hT : ∀ n, 2 ≤ n → ¬ 3 ∣ n → aval L (binWord (Collatz.Arctic.T n)) ≤ aval L (binWord n))
    (h3 : ∀ n, 1 ≤ n → 3 ∣ n → aval L (binWord n) = 0) (hG : 1 < Rigid.gDiag L.B) :
    ∃ (a : Q) (Ψ : List (Fin 2)) (h : ℕ) (c : ℝ), 1 ≤ h ∧ 0 < c ∧
      ∀ ε : List (Fin 2), c * Rigid.gDiag L.B ^ (Rigid.heavyWord Ψ h ε).length ≤
        Rigid.Dx L.B (Rigid.heavyWord Ψ h ε) a a :=
  top_heavy L hG (Rigid.diag_le_gDiag L.B) (lyap_compare L hall hT h3)

end Collatz.Arctic.NatQ5
