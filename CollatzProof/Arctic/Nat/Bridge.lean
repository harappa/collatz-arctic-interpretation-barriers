/-
# 𝒯: the bridge from orientation to values

Lemma 10.2 of the paper: (i) the identity for the decrease at one step, and its sum along a derivation; (ii) under weak orientation each term is at least 0, under strict orientation
at least `(M_p)₀₀`, and at least 1 if the interpretation is monotone; and (iii) the value `Φ(can n)` of canonical strings does not increase along steps of `T` (the natural-number
version of the arctic bridge; monotonicity is not used). Finally `NatValueCore → NatBarrierST` (the counterpart of the arctic `Main.arctic_barrier_ST`).

* The canonical derivation `canDeriv` and its correctness `canDeriv_chain` (`Canon.lean`), the membership of rules `canDeriv_sub` and the number of uses
  `usesOrbit_succ` (`Main.lean`), and the derivation chains `Chain` (`Bridge.lean`) are reused from the arctic part (the frozen files are not changed).
* Notation: `f_p := M_p^T e_o` (`rowN I p`, the row of forward values obtained by reading `p` from the left), `y_q := [q](0)`,
  `Δ_ρ(y) := [l](y) - [r](y)` (`deltaN`, with values in ℤ). The identities are written in ℤ; the forms as inequalities in ℕ (`phiN_step_le`, `phiN_step_strict`) are also given.
-/
import CollatzProof.Arctic.Nat.Statement
import CollatzProof.Arctic.Main

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Matrix

variable {d : ℕ}

/-! ## §1 Lemmas on composition -/

theorem NAff.comp_app (F G : NAff d) (y : Fin d → ℕ) : (F.comp G).app y = F.app (G.app y) := by
  simp only [NAff.comp, NAff.app, mulVec_add, mulVec_mulVec, add_assoc]

theorem NAff.id_app (y : Fin d → ℕ) : (NAff.id d).app y = y := by
  simp [NAff.id, NAff.app]

theorem NAff.comp_assoc (F G H : NAff d) : (F.comp G).comp H = F.comp (G.comp H) := by
  simp only [NAff.comp, NAff.mk.injEq]
  exact ⟨Matrix.mul_assoc _ _ _, by rw [mulVec_add, mulVec_mulVec, add_assoc]⟩

theorem NAff.id_comp (F : NAff d) : (NAff.id d).comp F = F := by
  cases F
  simp [NAff.comp, NAff.id]

/-- `evN` is the composition of maps: `[s₁ ⋯ sₙ](y) = [s₁](⋯ [sₙ](y))` (a copy of `NatExample.evN_app`). -/
theorem evN_app (I : Letter → NAff d) (y : Fin d → ℕ) :
    ∀ w : Word, (evN I w).app y = w.foldr (fun s z => (I s).app z) y
  | [] => by simp [evN, NAff.app, NAff.id]
  | s :: w => by
    rw [List.foldr_cons, ← evN_app I y w]
    simp only [evN, NAff.comp, NAff.app, mulVec_add, mulVec_mulVec, add_assoc]

theorem evN_append (I : Letter → NAff d) (u w : Word) : evN I (u ++ w) = (evN I u).comp (evN I w) := by
  induction u with
  | nil => simp [evN, NAff.id_comp]
  | cons s u ih => simp only [List.cons_append, evN, ih, NAff.comp_assoc]

theorem evN_append_app (I : Letter → NAff d) (u w : Word) (y : Fin d → ℕ) :
    (evN I (u ++ w)).app y = (evN I u).app ((evN I w).app y) := by
  rw [evN_append, NAff.comp_app]

theorem evN_singleton_app (I : Letter → NAff d) (s : Letter) (y : Fin d → ℕ) :
    (evN I [s]).app y = (I s).app y := by
  rw [evN_app]; rfl

/-! ## §2 Values and forward rows -/

theorem phiN_eq [NeZero d] (I : Letter → NAff d) (w : Word) : PhiN I w = (evN I w).v 0 := by
  simp [PhiN, NAff.app]

/-- The row of forward values `f_p := M_p^T e_o` (row 0 of the matrix of `p`). -/
def rowN [NeZero d] (I : Letter → NAff d) (p : Word) : Fin d → ℕ := fun i => (evN I p).M 0 i

/-- `f_p = e_o^T M_p` (the row vector carried by the matrix of `p`). -/
theorem rowN_eq_vecMul [NeZero d] (I : Letter → NAff d) (p : Word) :
    rowN I p = Pi.single 0 1 ᵥ* (evN I p).M := by
  funext i
  simp [rowN, vecMul, single_dotProduct]

/-- Reading `p` from the left: `f_{pu} = f_p M_u`. -/
theorem rowN_append [NeZero d] (I : Letter → NAff d) (p u : Word) :
    rowN I (p ++ u) = rowN I p ᵥ* (evN I u).M := by
  funext j
  simp only [rowN, evN_append, NAff.comp, Matrix.mul_apply, vecMul, dotProduct]

/-- The value in a context: `Φ(p w q) = f_p ⬝ [w](y_q) + (v_p)_o`. -/
theorem phiN_ctx [NeZero d] (I : Letter → NAff d) (p w q : Word) :
    PhiN I (p ++ w ++ q) = rowN I p ⬝ᵥ (evN I w).app ((evN I q).app 0) + (evN I p).v 0 := by
  unfold PhiN
  rw [List.append_assoc, evN_append_app, evN_append_app]
  rfl

/-! ## §3 Lemma 10.2 (i) (the identity for the decrease at one step) -/

/-- `Δ_ρ(y) := [l](y) - [r](y)` (with values in ℤ). -/
def deltaN (I : Letter → NAff d) (ρ : Rule) (y : Fin d → ℕ) : Fin d → ℤ :=
  fun i => ((evN I ρ.lhs).app y i : ℤ) - ((evN I ρ.rhs).app y i : ℤ)

/-- The term `f_p ⬝ Δ_ρ(y_q)` of the decrease at one step. -/
def stepTerm [NeZero d] (I : Letter → NAff d) (p : Word) (ρ : Rule) (q : Word) : ℤ :=
  ∑ i, (rowN I p i : ℤ) * deltaN I ρ ((evN I q).app 0) i

/-- **Lemma 10.2 (i)** (one step): `Φ(plq) - Φ(prq) = f_p ⬝ Δ_ρ(y_q)`. -/
theorem lemma_66_1_1 [NeZero d] (I : Letter → NAff d) (p q : Word) (ρ : Rule) :
    (PhiN I (p ++ ρ.lhs ++ q) : ℤ) - PhiN I (p ++ ρ.rhs ++ q) = stepTerm I p ρ q := by
  rw [phiN_ctx, phiN_ctx]
  unfold stepTerm deltaN dotProduct
  push_cast
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- Derivations with contexts: the `j`-th step is `p_j l_j q_j → p_j r_j q_j` (by the rule `ρ_j`). -/
inductive CtxChain : List (Word × Rule × Word) → Word → Word → Prop
  | nil (u : Word) : CtxChain [] u u
  | cons {p q v : Word} {ρ : Rule} {cs : List (Word × Rule × Word)} :
      CtxChain cs (p ++ ρ.rhs ++ q) v → CtxChain ((p, ρ, q) :: cs) (p ++ ρ.lhs ++ q) v

/-- **Lemma 10.2 (i)** (derivations): `Φ(w₀) - Φ(w_N) = Σ_j f_{p_j} ⬝ Δ_{ρ_j}(y_{q_j})` (telescoping). -/
theorem lemma_66_1_1_chain [NeZero d] (I : Letter → NAff d) :
    ∀ {cs : List (Word × Rule × Word)} {u v : Word}, CtxChain cs u v →
      (PhiN I u : ℤ) - PhiN I v = (cs.map fun c => stepTerm I c.1 c.2.1 c.2.2).sum := by
  intro cs u v h
  induction h with
  | nil u => simp
  | @cons p q v ρ cs _ ih =>
    rw [List.map_cons, List.sum_cons, ← ih, ← lemma_66_1_1]
    ring

/-- From the arctic `Chain` (derivations that do not record the contexts) to derivations with contexts. -/
theorem ctxChain_of_chain :
    ∀ {rs : List Rule} {u v : Word}, Chain rs u v →
      ∃ cs : List (Word × Rule × Word), CtxChain cs u v ∧ cs.map (fun c => c.2.1) = rs := by
  intro rs u v h
  induction h with
  | nil u => exact ⟨[], CtxChain.nil u, rfl⟩
  | @cons ρ rs u w v hstep _ ih =>
    obtain ⟨cs, hcs, hmap⟩ := ih
    obtain ⟨p, q, rfl, rfl⟩ := hstep
    exact ⟨(p, ρ, q) :: cs, CtxChain.cons hcs, by simp [hmap]⟩

/-! ## §4 Lemma 10.2 (ii) (lower bounds for the decrease at one use) -/

/-- Under weak orientation, `[r](y) ≤ [l](y)` (entrywise) for every `y`. -/
theorem app_le_of_weak {I : Letter → NAff d} {ρ : Rule} (hw : NWeak I ρ) (y : Fin d → ℕ) (i : Fin d) :
    (evN I ρ.rhs).app y i ≤ (evN I ρ.lhs).app y i := by
  unfold NAff.app
  simp only [Pi.add_apply]
  refine add_le_add ?_ (hw.2 i)
  simp only [mulVec, dotProduct]
  exact Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (hw.1 i j)

/-- Under strict orientation, `([r](y))_o + 1 ≤ ([l](y))_o` for every `y`. -/
theorem app0_lt_of_strict [NeZero d] {I : Letter → NAff d} {ρ : Rule} (hs : NStrict I ρ)
    (y : Fin d → ℕ) : (evN I ρ.rhs).app y 0 < (evN I ρ.lhs).app y 0 := by
  have hM : (evN I ρ.rhs).M *ᵥ y ≤ (evN I ρ.lhs).M *ᵥ y := by
    intro i
    simp only [mulVec, dotProduct]
    exact Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (hs.1.1 i j)
  unfold NAff.app
  simp only [Pi.add_apply]
  exact Nat.add_lt_add_of_le_of_lt (hM 0) hs.2

/-- If the interpretation is monotone, `(M_p)₀₀ ≥ 1` (the `(o, o)` entry of a product of non-negative matrices is at least the product of the diagonal entries). -/
theorem evN_M00_pos [NeZero d] {I : Letter → NAff d} (hmono : NMono I) : ∀ p : Word, 1 ≤ (evN I p).M 0 0
  | [] => by simp [evN, NAff.id]
  | s :: p => by
    have ih := evN_M00_pos hmono p
    simp only [evN, NAff.comp, Matrix.mul_apply]
    calc 1 ≤ (I s).M 0 0 * (evN I p).M 0 0 := Nat.one_le_iff_ne_zero.mpr
            (Nat.mul_ne_zero (by have := hmono s; omega) (by omega))
      _ ≤ ∑ k, (I s).M 0 k * (evN I p).M k 0 :=
            Finset.single_le_sum (f := fun k => (I s).M 0 k * (evN I p).M k 0)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)

/-- **Lemma 10.2 (ii)**, first part: the term of a weakly oriented rule is at least 0. -/
theorem stepTerm_nonneg [NeZero d] {I : Letter → NAff d} {ρ : Rule} (hw : NWeak I ρ) (p q : Word) :
    0 ≤ stepTerm I p ρ q :=
  Finset.sum_nonneg fun i _ =>
    mul_nonneg (by positivity) (sub_nonneg.mpr (by exact_mod_cast app_le_of_weak hw _ i))

/-- **Lemma 10.2 (ii)**, second part: the term of a strictly oriented rule is at least `(M_p)₀₀`. -/
theorem stepTerm_ge [NeZero d] {I : Letter → NAff d} {ρ : Rule} (hs : NStrict I ρ) (p q : Word) :
    ((evN I p).M 0 0 : ℤ) ≤ stepTerm I p ρ q := by
  unfold stepTerm
  have hδ : ∀ i, 0 ≤ deltaN I ρ ((evN I q).app 0) i := fun i =>
    sub_nonneg.mpr (by exact_mod_cast app_le_of_weak hs.1 _ i)
  have h0 : 1 ≤ deltaN I ρ ((evN I q).app 0) 0 := by
    have := app0_lt_of_strict hs ((evN I q).app 0)
    unfold deltaN
    omega
  calc ((evN I p).M 0 0 : ℤ) = (rowN I p 0 : ℤ) * 1 := by simp [rowN]
    _ ≤ (rowN I p 0 : ℤ) * deltaN I ρ ((evN I q).app 0) 0 :=
        mul_le_mul_of_nonneg_left h0 (by positivity)
    _ ≤ ∑ i, (rowN I p i : ℤ) * deltaN I ρ ((evN I q).app 0) i :=
        Finset.single_le_sum (f := fun i => (rowN I p i : ℤ) * deltaN I ρ ((evN I q).app 0) i)
          (fun i _ => mul_nonneg (by positivity) (hδ i)) (Finset.mem_univ 0)

/-- **Lemma 10.2 (ii)**, last part: if the interpretation is monotone, the term of a strictly oriented rule is at least 1. -/
theorem stepTerm_ge_one [NeZero d] {I : Letter → NAff d} (hmono : NMono I) {ρ : Rule} (hs : NStrict I ρ)
    (p q : Word) : 1 ≤ stepTerm I p ρ q := by
  have h1 := stepTerm_ge hs p q
  have h2 : (1 : ℤ) ≤ (evN I p).M 0 0 := by exact_mod_cast evN_M00_pos hmono p
  omega

/-! ## §5 The forms as inequalities in ℕ, and bounds along derivations -/

/-- Under weak orientation, `Φ` in a context does not increase (monotonicity is not used). -/
theorem phiN_step_le [NeZero d] {I : Letter → NAff d} {ρ : Rule} (hw : NWeak I ρ) (p q : Word) :
    PhiN I (p ++ ρ.rhs ++ q) ≤ PhiN I (p ++ ρ.lhs ++ q) := by
  have h1 := lemma_66_1_1 I p q ρ
  have h2 := stepTerm_nonneg hw p q
  omega

/-- Under monotonicity and strict orientation, `Φ` in a context decreases by at least 1. -/
theorem phiN_step_strict [NeZero d] {I : Letter → NAff d} (hmono : NMono I) {ρ : Rule} (hs : NStrict I ρ)
    (p q : Word) : PhiN I (p ++ ρ.rhs ++ q) + 1 ≤ PhiN I (p ++ ρ.lhs ++ q) := by
  have h1 := lemma_66_1_1 I p q ρ
  have h2 := stepTerm_ge_one hmono hs p q
  omega

/-- Along a derivation by weakly oriented rules only, `Φ` does not increase. -/
theorem phiN_chain_le [NeZero d] (I : Letter → NAff d) :
    ∀ {rs : List Rule} {u v : Word}, Chain rs u v → (∀ σ ∈ rs, NWeak I σ) → PhiN I v ≤ PhiN I u := by
  intro rs u v hc
  induction hc with
  | nil u => intro _; exact le_rfl
  | @cons σ rs u w v hstep _ ih =>
    intro hw
    obtain ⟨p, q, rfl, rfl⟩ := hstep
    exact (ih (fun τ hτ => hw τ (List.mem_cons_of_mem _ hτ))).trans
      (phiN_step_le (hw σ List.mem_cons_self) p q)

/-- A bound along derivations: if the interpretation is monotone, `Φ` decreases by at least the number of uses of the strictly oriented rule `ρ`. -/
theorem phiN_chain_count [NeZero d] {I : Letter → NAff d} (hmono : NMono I) {ρ : Rule} (hρ : NStrict I ρ) :
    ∀ {rs : List Rule} {u v : Word}, Chain rs u v → (∀ σ ∈ rs, NWeak I σ) →
      PhiN I v + rs.count ρ ≤ PhiN I u := by
  intro rs u v hc
  induction hc with
  | nil u => intro _; simp
  | @cons σ rs u w v hstep _ ih =>
    intro hw
    have hrest := ih (fun τ hτ => hw τ (List.mem_cons_of_mem _ hτ))
    obtain ⟨p, q, rfl, rfl⟩ := hstep
    by_cases hσ : σ = ρ
    · subst hσ
      have h1 := phiN_step_strict hmono hρ p q
      rw [List.count_cons_self]
      omega
    · have h1 := phiN_step_le (hw σ List.mem_cons_self) p q
      rw [List.count_cons_of_ne hσ]
      omega

/-! ## §6 Values of canonical strings (Lemma 10.2 (iii), the natural-number version of the arctic bridge) -/

/-- **Lemma 10.2 (iii)** (first part): for a natural-number matrix interpretation that weakly orients all 11 rules of 𝒯 (monotonicity is not used),
`Φ(can (T n)) ≤ Φ(can n)` for `n ≥ 2`. -/
theorem phiN_can_T_le [NeZero d] {I : Letter → NAff d} (hweak : ∀ ρ ∈ rulesST, NWeak I ρ) (n : ℕ)
    (hn : 2 ≤ n) : PhiN I (can (T n)) ≤ PhiN I (can n) :=
  phiN_chain_le I (canDeriv_chain n hn) (fun σ hσ => hweak σ (canDeriv_sub n σ hσ))

/-- On a segment of an orbit (all points at least 2), `Φ(can ·)` does not increase. -/
theorem phiN_can_iterate_le [NeZero d] {I : Letter → NAff d} (hweak : ∀ ρ ∈ rulesST, NWeak I ρ) :
    ∀ (m n : ℕ), (∀ i < m, 2 ≤ T^[i] n) → PhiN I (can (T^[m] n)) ≤ PhiN I (can n) := by
  intro m
  induction m with
  | zero => intro n _; simp
  | succ m ih =>
    intro n horb
    have hn : 2 ≤ n := by simpa using horb 0 (Nat.succ_pos m)
    have horb' : ∀ i < m, 2 ≤ T^[i] (T n) := by
      intro i hi
      have := horb (i + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    rw [Function.iterate_succ_apply]
    exact (ih (T n) horb').trans (phiN_can_T_le hweak n hn)

/-- A bound along orbits (Lemma 10.2 (iii)): if the interpretation is monotone, weakly orients the 11 rules and strictly orients `ρ`, then
`Φ(can (T^m n)) + (the number of uses of ρ) ≤ Φ(can n)`. -/
theorem orbit_bound_nat [NeZero d] {I : Letter → NAff d} (hmono : NMono I)
    (hweak : ∀ ρ ∈ rulesST, NWeak I ρ) {ρ : Rule} (hρ : NStrict I ρ) :
    ∀ (m n : ℕ), (∀ i < m, 2 ≤ T^[i] n) → PhiN I (can (T^[m] n)) + usesOrbit ρ n m ≤ PhiN I (can n) := by
  intro m
  induction m with
  | zero => intro n _; simp [usesOrbit_zero]
  | succ m ih =>
    intro n horb
    have hn : 2 ≤ n := by simpa using horb 0 (Nat.succ_pos m)
    have hstep := phiN_chain_count hmono hρ (canDeriv_chain n hn)
      (fun σ hσ => hweak σ (canDeriv_sub n σ hσ))
    have horb' : ∀ i < m, 2 ≤ T^[i] (T n) := by
      intro i hi
      have := horb (i + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    have hrest := ih (T n) horb'
    rw [Function.iterate_succ_apply, usesOrbit_succ]
    unfold uses
    omega

/-! ## §7 The main theorem from the value-level hypothesis -/

/-- **The main theorem** (the part of Theorem 9.2 (i) on the rewriting system 𝒯): `NatBarrierST` under the value-level hypothesis `NatValueCore`. -/
theorem natBarrierST_of_core (hcore : NatValueCore) : NatBarrierST := by
  intro d _ I hmono hweak ρ hρmem hρ
  obtain ⟨n, -, m, horb, hlt⟩ := hcore d I hmono hweak ρ hρmem 0
  have := orbit_bound_nat hmono hweak hρ m n horb
  omega

end Collatz.Arctic.NatQ5
