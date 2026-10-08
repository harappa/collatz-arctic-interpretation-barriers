/-
# Corollary 10.12 (the corner form of [HW06]): at a corner of indices with diagonal entries at least 1, no rule decreases strictly (end of Section 10)

A point of internal review: the form of Hofbauer–Waldmann (HW06) that compares corner entries follows in a few lines from the kernel-checked Theorem 10.11 (ii)
(the value-level core for general families `GenValueCore`, `Embed.lean`). We write the argument of the proof of Corollary 10.12
for an arbitrary subset `J` of the indices.

* §1 Statements: for a family `N_s` (7 letters) of square natural-number matrices over a finite type of indices `ι` and a subset `J` of the indices with
  `(N_s)_{ii} ≥ 1` for every letter and every `i ∈ J`, if `N` weakly orients all 11 rules of $\mathcal T$ entrywise (`GWeak`, `N_ℓ ≥ N_r`), then no rule decreases
  strictly at an entry of `J × J` (a corner) (`HWBarrierST`). The same holds for the reversed system $\mathcal T^{\mathrm{rev}}$ (`HWBarrierSTrev`; products of strings
  are taken in the same direction as for the forward system, `N_w = N_{w₁} ⋯ N_{w_k}`, by the convention of `StatementRev.lean`).
* §2 The decrease at one use (the matrix version of Lemma 10.2 (ii) of the paper): if `(N_r)_{ij} < (N_ℓ)_{ij}` with `i, j ∈ J`, then a step `pℓq → prq` gives
  `(N_{pℓq})_{ij} - (N_{prq})_{ij} ≥ (N_p)_{ii}(N_ℓ - N_r)_{ij}(N_q)_{jj} ≥ 1` (`nw_step_lt`). The bound `(N_p)_{ii} ≥ 1` is kept by products of non-negative
  matrices with diagonal entries at least 1 (`nw_diag_pos`). Steps by other rules do not increase the entry (`nw_step_le` of `ValueAuto.lean`).
* §3 The bound along orbits (the matrix version of Lemma 10.2 (iii) of the paper): `(N_{can (T^m n)})_{ij} + #_ρ(n, m) ≤ (N_{can n})_{ij}`
  (`orbit_bound_corner`; a copy of `phiN_chain_count` and `orbit_bound_nat` of `Bridge.lean`).
* §4 The main theorems: Theorem 10.11 (ii) with `a = i` and `z = j` gives `n, m` with `(N_{can n})_{ij} < #_ρ(n, m)`, contradicting §3
  (`hwBarrierST_of_genCore`). The reversed system is reduced to the forward one by transposition (`hwBarrierSTrev_of_ST`: `N'_s := N_s^T` weakly orients `ρ`
  ⟺ `N` weakly orients `ρ^rev` (`gweak_transpose_iff` of `Embed.lean`), `(N'_ℓ)_{ji} = (N_{ℓ^rev})_{ij}`
  (`NW_transpose`), and transposition keeps the diagonal). The forms without hypotheses, `hwBarrierST` and `hwBarrierSTrev`, follow from
  `genValueCore_of_autoValueCore W4a.autoValueCore` (the same term as `paper_thm_10_11_gen` of the paper).
* §5 The contained form: for the family `homFam I` of homogeneous matrices of a natural-number matrix interpretation (`J = {0, d}`), monotonicity is the condition
  on the diagonal of `J`, and `NStrict` is a strict decrease at the corner `(0, d)`. Hence the frozen `NatBarrierST` and `NatBarrierSTrev` are special cases of
  `HWBarrierST` and `HWBarrierSTrev` (`natBarrierST_of_hw`, `natBarrierSTrev_of_hw`; a check of the statements; the proof without hypotheses still goes through `Final.lean`).

The non-vacuity checks are in `NonVacuityHW.lean` (outside the closure of the main theorem).
-/
import CollatzProof.Arctic.Nat.H2MainExtra

namespace Collatz.Arctic.NatQ5.HW

open Collatz.Arctic Collatz.Arctic.NatQ5 Matrix

set_option linter.unusedSectionVars false

/-! ## §1 Statements -/

/-- **The statement of Corollary 10.12 ($\mathcal T$, the corner form of [HW06])**: for a family `N` (7 letters) of square natural-number matrices over a finite
type of indices `ι` and a subset `J` of the indices with `(N_s)_{ii} ≥ 1` for every letter `s` and every `i ∈ J` that weakly orients all 11 rules of $\mathcal T$ entrywise
(`N_ℓ ≥ N_r`, `GWeak`), no rule `ℓ → r` has `(N_r)_{ij} < (N_ℓ)_{ij}` at an entry with `i, j ∈ J`. Products of strings are
`N_w = N_{w₁} ⋯ N_{w_k}` (`NW`).

**Correspondence with the form of HW06**: the form `E_{\{1,d\}}` of the matrix interpretations of Hofbauer–Waldmann (HW06) (as summarized in EWZ08, §6, p. 207: the
entries `(1,1)` and `(d,d)` of the `d × d` matrix of every letter are positive, `L ≥ R` (entrywise) for all rules, and a rule is strictly oriented if `L > R` at one
of the four corners `{1,d} × {1,d}`) is the case `J = {1, d}`. The conclusion is that such an interpretation that weakly orients all 11 rules of $\mathcal T$
strictly orients none of them. `J` may be any subset (a single index, or all `d` indices).

**Not covered**: the core form of Thiemann–Hofbauer–Le Huitouze–Waldmann (FSCD 2026) (Property 1: `α(u)(α(ℓ) - α(r))α(v) > 0` for strict rules
and `≥ 0` for weak rules; it does not ask for `N_ℓ ≥ N_r` entrywise) is outside this statement. -/
def HWBarrierST : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : Letter → Matrix ι ι ℕ) (J : Finset ι),
    (∀ s, ∀ i ∈ J, 1 ≤ N s i i) → (∀ ρ ∈ rulesST, GWeak N ρ) →
    ∀ ρ ∈ rulesST, ∀ i ∈ J, ∀ j ∈ J, ¬ NW N ρ.rhs i j < NW N ρ.lhs i j

/-- **The statement of Corollary 10.12 ($\mathcal T^{\mathrm{rev}}$, the corner form of [HW06])**: `HWBarrierST` with the set of rules replaced by the reversed system
$\mathcal T^{\mathrm{rev}}$ (`rulesSTrev`, `StatementRev.lean`). Products of strings are taken in the same direction as for the forward system, by convention 2 of `StatementRev.lean`
(`N_w = N_{w₁} ⋯ N_{w_k}`); for instance, the left-hand side of `.t → .2` is `N_. N_t`. The form `E_{\{1,d\}}` of HW06 is the case `J = {1, d}`, and
the core form (Property 1 of FSCD 2026) is outside the statement (as in the comment on `HWBarrierST`). -/
def HWBarrierSTrev : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : Letter → Matrix ι ι ℕ) (J : Finset ι),
    (∀ s, ∀ i ∈ J, 1 ≤ N s i i) → (∀ ρ ∈ rulesSTrev, GWeak N ρ) →
    ∀ ρ ∈ rulesSTrev, ∀ i ∈ J, ∀ j ∈ J, ¬ NW N ρ.rhs i j < NW N ρ.lhs i j

/-! ## §2 The decrease at one use -/

section Step

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Multiplying by a non-negative matrix on the left keeps a strict inequality at the entry `(i, j)` (when `P_{ii} ≥ 1`). -/
theorem mul_lt_mul_entry_left {P A A' : Matrix ι ι ℕ} (h : ∀ k l, A k l ≤ A' k l) {i j : ι} (hP : 1 ≤ P i i)
    (hlt : A i j < A' i j) : (P * A) i j < (P * A') i j := by
  simp only [Matrix.mul_apply]
  exact Finset.sum_lt_sum (fun k _ => Nat.mul_le_mul_left _ (h k j))
    ⟨i, Finset.mem_univ _, Nat.mul_lt_mul_of_pos_left hlt hP⟩

/-- Multiplying by a non-negative matrix on the right keeps a strict inequality at the entry `(i, j)` (when `Q_{jj} ≥ 1`). -/
theorem mul_lt_mul_entry_right {A A' Q : Matrix ι ι ℕ} (h : ∀ k l, A k l ≤ A' k l) {i j : ι} (hQ : 1 ≤ Q j j)
    (hlt : A i j < A' i j) : (A * Q) i j < (A' * Q) i j := by
  simp only [Matrix.mul_apply]
  exact Finset.sum_lt_sum (fun k _ => Nat.mul_le_mul_right _ (h i k))
    ⟨j, Finset.mem_univ _, Nat.mul_lt_mul_of_pos_right hlt hQ⟩

variable {N : Letter → Matrix ι ι ℕ} {J : Finset ι}

/-- **Diagonal**: if the diagonal entries of `J` are at least 1 for all letters, they are at least 1 for the product of every string (`(N_w)_{ii}` is at least the weight
`(N_{w₁})_{ii} ⋯ (N_{w_k})_{ii}` of the path that stays at `i`; the matrix version of `evN_M00_pos` of `Bridge.lean`). -/
theorem nw_diag_pos (hdiag : ∀ s, ∀ i ∈ J, 1 ≤ N s i i) : ∀ (w : Word) (i : ι), i ∈ J → 1 ≤ NW N w i i
  | [], i, _ => by simp
  | s :: w, i, hi => by
    have ih := nw_diag_pos hdiag w i hi
    have hs := hdiag s i hi
    rw [NW_cons, Matrix.mul_apply]
    calc 1 ≤ N s i i * NW N w i i := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      _ ≤ ∑ k, N s i k * NW N w k i :=
          Finset.single_le_sum (f := fun k => N s i k * NW N w k i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- **The decrease at one use** (the matrix version of Lemma 10.2 (ii) of the paper): if `ρ` is weakly oriented and decreases strictly at an entry with `i, j ∈ J`,
then a step `pℓq → prq` in a context decreases the entry `(i, j)` by at least 1
(`(N_{pℓq})_{ij} - (N_{prq})_{ij} ≥ (N_p)_{ii}(N_ℓ - N_r)_{ij}(N_q)_{jj} ≥ 1`). -/
theorem nw_step_lt (hdiag : ∀ s, ∀ i ∈ J, 1 ≤ N s i i) {ρ : Rule} (hw : GWeak N ρ) {i j : ι} (hi : i ∈ J)
    (hj : j ∈ J) (hlt : NW N ρ.rhs i j < NW N ρ.lhs i j) (p q : Word) :
    NW N (p ++ ρ.rhs ++ q) i j < NW N (p ++ ρ.lhs ++ q) i j := by
  rw [NW_append, NW_append, NW_append, NW_append]
  exact mul_lt_mul_entry_right (fun k l => mul_le_mul_entry hw k l) (nw_diag_pos hdiag q j hj)
    (mul_lt_mul_entry_left hw (nw_diag_pos hdiag p i hi) hlt)

end Step

/-! ## §3 Derivations and the bound along orbits -/

section Orbit

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : Letter → Matrix ι ι ℕ} {J : Finset ι}

/-- The bound along derivations: in a derivation by weakly oriented rules only, the entry `(i, j)` decreases at least by the number of uses of a rule `ρ` that decreases
strictly at the entry `(i, j)` of `J × J` (a copy of `phiN_chain_count` of `Bridge.lean`). -/
theorem nw_chain_count (hdiag : ∀ s, ∀ i ∈ J, 1 ≤ N s i i) {ρ : Rule} {i j : ι} (hi : i ∈ J) (hj : j ∈ J)
    (hlt : NW N ρ.rhs i j < NW N ρ.lhs i j) :
    ∀ {rs : List Rule} {u v : Word}, Chain rs u v → (∀ σ ∈ rs, GWeak N σ) →
      NW N v i j + rs.count ρ ≤ NW N u i j := by
  intro rs u v hc
  induction hc with
  | nil u => intro _; simp
  | @cons σ rs u w v hstep _ ih =>
    intro hw
    have hrest := ih (fun τ hτ => hw τ (List.mem_cons_of_mem _ hτ))
    obtain ⟨p, q, rfl, rfl⟩ := hstep
    by_cases hσ : σ = ρ
    · subst hσ
      have h1 := nw_step_lt hdiag (hw σ List.mem_cons_self) hi hj hlt p q
      rw [List.count_cons_self]
      omega
    · have h1 := nw_step_le (hw σ List.mem_cons_self) p q i j
      rw [List.count_cons_of_ne hσ]
      omega

/-- **The bound along orbits** (the matrix version of Lemma 10.2 (iii) of the paper): if the diagonal entries of `J` are at least 1, the 11 rules are weakly oriented,
and `ρ` decreases strictly at the entry `(i, j)` of `J × J`, then `(N_{can (T^m n)})_{ij} + #_ρ(n, m) ≤ (N_{can n})_{ij}` (all points of the segment of the orbit
are at least 2; a copy of `orbit_bound_nat` of `Bridge.lean`). -/
theorem orbit_bound_corner (hdiag : ∀ s, ∀ i ∈ J, 1 ≤ N s i i) (hweak : ∀ ρ ∈ rulesST, GWeak N ρ) {ρ : Rule}
    {i j : ι} (hi : i ∈ J) (hj : j ∈ J) (hlt : NW N ρ.rhs i j < NW N ρ.lhs i j) :
    ∀ (m n : ℕ), (∀ k < m, 2 ≤ T^[k] n) → NW N (can (T^[m] n)) i j + usesOrbit ρ n m ≤ NW N (can n) i j := by
  intro m
  induction m with
  | zero => intro n _; simp [usesOrbit_zero]
  | succ m ih =>
    intro n horb
    obtain ⟨hn, horb'⟩ := W5.orbit_tail horb
    have hstep := nw_chain_count hdiag hi hj hlt (canDeriv_chain n hn)
      (fun σ hσ => hweak σ (canDeriv_sub n σ hσ))
    have hrest := ih (T n) horb'
    rw [Function.iterate_succ_apply, usesOrbit_succ]
    unfold uses
    omega

end Orbit

/-! ## §4 The main theorems -/

/-- **Corollary 10.12 ($\mathcal T$) from the value-level core for general families**: `HWBarrierST` under `GenValueCore` (Theorem 10.11 (ii)). -/
theorem hwBarrierST_of_genCore (hcore : GenValueCore) : HWBarrierST := by
  intro ι _ _ N J hdiag hweak ρ hρ i hi j hj hlt
  obtain ⟨n, -, m, horb, hcmp⟩ := hcore ι N i j hweak ρ hρ 0
  have := orbit_bound_corner hdiag hweak hi hj hlt m n horb
  omega

/-- **The reversed system is reduced to the forward one by transposition**: `N'_s := N_s^T` keeps the condition on the diagonal of `J` and weakly orients the 11 rules
of $\mathcal T$ (since `N` weakly orients the 11 rules of $\mathcal T^{\mathrm{rev}}$; `gweak_transpose_iff`). The entry `(i, j)` of `ρ^rev` is the entry `(j, i)` of `ρ`
for `N'` (`NW_transpose`). -/
theorem hwBarrierSTrev_of_ST (h : HWBarrierST) : HWBarrierSTrev := by
  intro ι _ _ N J hdiag hweak ρ' hρ' i hi j hj hlt
  obtain ⟨ρ, hρ, rfl⟩ := W5.mem_rulesSTrev hρ'
  have hweak' : ∀ σ ∈ rulesST, GWeak (fun s => (N s)ᵀ) σ := fun σ hσ =>
    (gweak_transpose_iff N σ).2 (hweak _ (W5.ruleRev_mem_rulesSTrev hσ))
  have hdiag' : ∀ s, ∀ k ∈ J, 1 ≤ (fun s => (N s)ᵀ) s k k := fun s k hk => by
    simpa only [Matrix.transpose_apply] using hdiag s k hk
  apply h ι (fun s => (N s)ᵀ) J hdiag' hweak' ρ hρ j hj i hi
  rw [NW_transpose, NW_transpose, Matrix.transpose_apply, Matrix.transpose_apply]
  exact hlt

/-- **Corollary 10.12 ($\mathcal T$) without hypotheses**: from the kernel-checked term of Theorem 10.11 (ii) (the same
`genValueCore_of_autoValueCore W4a.autoValueCore` as in `paper_thm_10_11_gen`). -/
theorem hwBarrierST : HWBarrierST :=
  hwBarrierST_of_genCore (genValueCore_of_autoValueCore W4a.autoValueCore)

/-- **Corollary 10.12 ($\mathcal T^{\mathrm{rev}}$) without hypotheses**. -/
theorem hwBarrierSTrev : HWBarrierSTrev := hwBarrierSTrev_of_ST hwBarrierST

/-! ## §5 The contained form: natural-number matrix interpretations (a check of the statements) -/

section Affine

variable {d : ℕ}

/-- The corner entry `(0, d)` of the family of homogeneous matrices is the component 0 of `v` (the first component of `[w](0)`). -/
theorem nw_homFam_corner [NeZero d] (I : Letter → NAff d) (w : Word) :
    NW (homFam I) w (some 0) none = (evN I w).v 0 := by
  rw [← homN_evN]; rfl

/-- The family of homogeneous matrices of a monotone natural-number matrix interpretation satisfies the condition on the diagonal for `J = {0, d}` (the index `some 0` and the homogeneous index `none`). -/
theorem homFam_diag [NeZero d] {I : Letter → NAff d} (hmono : NMono I) :
    ∀ s, ∀ i ∈ ({some 0, none} : Finset (Option (Fin d))), 1 ≤ homFam I s i i := by
  intro s i hi
  rcases Finset.mem_insert.1 hi with rfl | hi
  · exact hmono s
  · rw [Finset.mem_singleton.1 hi]; exact le_rfl

/-- **`HWBarrierST` contains the frozen `NatBarrierST`** (`J = {0, d}`; the second component of strict orientation `NStrict` is the strict decrease at the corner
`(0, d)`). -/
theorem natBarrierST_of_hw (h : HWBarrierST) : NatBarrierST := by
  intro d _ I hmono hweak ρ hρ hs
  refine h (Option (Fin d)) (homFam I) {some 0, none} (homFam_diag hmono)
    (fun σ hσ => gweak_of_nweak (hweak σ hσ)) ρ hρ (some 0) (by simp) none (by simp) ?_
  rw [nw_homFam_corner, nw_homFam_corner]
  exact hs.2

/-- **`HWBarrierSTrev` contains the frozen `NatBarrierSTrev`** (the same family; only the set of rules is `rulesSTrev`). -/
theorem natBarrierSTrev_of_hw (h : HWBarrierSTrev) : NatBarrierSTrev := by
  intro d _ I hmono hweak ρ hρ hs
  refine h (Option (Fin d)) (homFam I) {some 0, none} (homFam_diag hmono)
    (fun σ hσ => gweak_of_nweak (hweak σ hσ)) ρ hρ (some 0) (by simp) none (by simp) ?_
  rw [nw_homFam_corner, nw_homFam_corner]
  exact hs.2

end Affine

end Collatz.Arctic.NatQ5.HW
