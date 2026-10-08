/-
# 𝒯: generalizing the index of monotonicity (permutation of coordinates; a remark of the internal review)

The statement `NatBarrierST` fixes the index `o` of monotonicity to the Lean index `0` (monotonicity `(M_s)₀₀ ≥ 1`; strict orientation is strict in the
0-th component of `v`). YAH §2.3.1 also fixes it to the index 1. Here we show, by the permutation of coordinates
`σ = (0 k)`, that the form with any index `k` is the same statement (a corollary outside the closure of the main theorem).

* `NAff.perm σ F := ⟨M.submatrix σ σ, v ∘ σ⟩` (`F' (y) = F(y ∘ σ⁻¹) ∘ σ`). It preserves composition and the identity map (`NAff.perm_comp`,
  `NAff.perm_id`), so the interpretation of words is carried over by the permutation as well (`evN_perm`).
* Weak orientation does not change under the permutation (`nweak_perm_iff`), and monotonicity and strict orientation at the index 0 of the permuted interpretation are
  those at the index `σ 0` of the original interpretation (`nmono_perm_iff`, `nstrict_perm_iff`).
* `NatBarrierSTAt` (any dimension and any index `k`) is equivalent to `NatBarrierST` (`natBarrierST_iff_at`). The same holds for the statement
  `NatBarrierSTB` for the left-end rules (`natBarrierSTB_iff_at`).
-/
import CollatzProof.Arctic.Nat.Statement
import CollatzProof.Arctic.Nat.Bridge

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Matrix

variable {d : ℕ}

/-! ## §1 Permutation of coordinates -/

/-- The affine map transported by the permutation of coordinates `σ`: `M' = M.submatrix σ σ`, `v' = v ∘ σ`. -/
def NAff.perm (σ : Equiv.Perm (Fin d)) (F : NAff d) : NAff d := ⟨F.M.submatrix σ σ, F.v ∘ σ⟩

theorem NAff.perm_comp (σ : Equiv.Perm (Fin d)) (F G : NAff d) :
    (F.comp G).perm σ = (F.perm σ).comp (G.perm σ) := by
  simp only [NAff.perm, NAff.comp, NAff.mk.injEq]
  refine ⟨Matrix.submatrix_mul _ _ _ _ _ σ.bijective, ?_⟩
  rw [Matrix.submatrix_mulVec_equiv]
  funext i
  simp [Function.comp_def]

theorem NAff.perm_id (σ : Equiv.Perm (Fin d)) : (NAff.id d).perm σ = NAff.id d := by
  simp only [NAff.perm, NAff.id, NAff.mk.injEq, Matrix.submatrix_one_equiv, true_and]
  rfl

/-- The interpretation of words is carried over by the permutation. -/
theorem evN_perm (σ : Equiv.Perm (Fin d)) (I : Letter → NAff d) :
    ∀ w : Word, evN (fun s => (I s).perm σ) w = (evN I w).perm σ
  | [] => (NAff.perm_id σ).symm
  | s :: w => by
    show ((I s).perm σ).comp (evN (fun s => (I s).perm σ) w) = ((I s).comp (evN I w)).perm σ
    rw [evN_perm σ I w, NAff.perm_comp]

/-! ## §2 How orientation and monotonicity are carried over -/

theorem nweak_perm_iff (σ : Equiv.Perm (Fin d)) (I : Letter → NAff d) (ρ : Rule) :
    NWeak (fun s => (I s).perm σ) ρ ↔ NWeak I ρ := by
  unfold NWeak
  rw [evN_perm, evN_perm]
  simp only [NAff.perm, Matrix.submatrix_apply, Function.comp_apply]
  constructor
  · rintro ⟨hM, hv⟩
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · simpa using hM (σ.symm i) (σ.symm j)
    · simpa using hv (σ.symm i)
  · rintro ⟨hM, hv⟩
    exact ⟨fun i j => hM (σ i) (σ j), fun i => hv (σ i)⟩

/-- Monotonicity with the index `k`: `(M_s)_{kk} ≥ 1` for every letter. -/
def NMonoAt (k : Fin d) (I : Letter → NAff d) : Prop := ∀ s, 1 ≤ (I s).M k k

/-- Strict orientation with the index `k`: weak orientation, and the `k`-th component of `v` is strictly larger. -/
def NStrictAt (k : Fin d) (I : Letter → NAff d) (ρ : Rule) : Prop :=
  NWeak I ρ ∧ (evN I ρ.rhs).v k < (evN I ρ.lhs).v k

theorem nmonoAt_zero [NeZero d] (I : Letter → NAff d) : NMonoAt 0 I ↔ NMono I := Iff.rfl

theorem nstrictAt_zero [NeZero d] (I : Letter → NAff d) (ρ : Rule) : NStrictAt 0 I ρ ↔ NStrict I ρ := Iff.rfl

theorem nmono_perm_iff [NeZero d] (σ : Equiv.Perm (Fin d)) (I : Letter → NAff d) :
    NMono (fun s => (I s).perm σ) ↔ NMonoAt (σ 0) I := Iff.rfl

theorem nstrict_perm_iff [NeZero d] (σ : Equiv.Perm (Fin d)) (I : Letter → NAff d) (ρ : Rule) :
    NStrict (fun s => (I s).perm σ) ρ ↔ NStrictAt (σ 0) I ρ := by
  unfold NStrict NStrictAt
  rw [nweak_perm_iff, evN_perm, evN_perm]
  rfl

/-! ## §3 The statement with a general index -/

/-- The statement with any index `k` of monotonicity (`d ≥ 1` follows from `k : Fin d`). -/
def NatBarrierSTAt : Prop :=
  ∀ (d : ℕ) (k : Fin d) (I : Letter → NAff d), NMonoAt k I → (∀ ρ ∈ rulesST, NWeak I ρ) →
    ∀ ρ ∈ rulesST, ¬ NStrictAt k I ρ

/-- The form of the statement for the left-end rules with any index `k`. -/
def NatBarrierSTBAt : Prop :=
  ∀ (d : ℕ) (k : Fin d) (I : Letter → NAff d), (∀ ρ ∈ rulesST, NWeak I ρ) →
    ∀ ρ ∈ rulesSTB, ¬ NStrictAt k I ρ

theorem neZero_of_fin (k : Fin d) : NeZero d := ⟨by rintro rfl; exact k.elim0⟩

/-- **Generalizing the index of monotonicity**: `NatBarrierST` (index 0) is equivalent to the form with any index `k`. -/
theorem natBarrierST_iff_at : NatBarrierST ↔ NatBarrierSTAt := by
  constructor
  · intro h d k I hmono hweak ρ hρ hs
    have := neZero_of_fin k
    let σ : Equiv.Perm (Fin d) := Equiv.swap 0 k
    have hσ0 : σ 0 = k := Equiv.swap_apply_left 0 k
    refine h d (fun s => (I s).perm σ) ?_ (fun τ hτ => (nweak_perm_iff σ I τ).2 (hweak τ hτ)) ρ hρ ?_
    · rw [nmono_perm_iff, hσ0]; exact hmono
    · rw [nstrict_perm_iff, hσ0]; exact hs
  · intro h d _ I hmono hweak ρ hρ hs
    exact h d 0 I hmono hweak ρ hρ hs

/-- The statement for the left-end rules is also equivalent to the form with any index `k`. -/
theorem natBarrierSTB_iff_at : NatBarrierSTB ↔ NatBarrierSTBAt := by
  constructor
  · intro h d k I hweak ρ hρ hs
    have := neZero_of_fin k
    let σ : Equiv.Perm (Fin d) := Equiv.swap 0 k
    have hσ0 : σ 0 = k := Equiv.swap_apply_left 0 k
    refine h d (fun s => (I s).perm σ) (fun τ hτ => (nweak_perm_iff σ I τ).2 (hweak τ hτ)) ρ hρ ?_
    rw [nstrict_perm_iff, hσ0]; exact hs
  · intro h d _ I hweak ρ hρ hs
    exact h d 0 I hweak ρ hρ hs

end Collatz.Arctic.NatQ5
