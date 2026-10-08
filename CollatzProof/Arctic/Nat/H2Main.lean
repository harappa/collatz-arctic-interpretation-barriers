/-
# Theorem 10.8 and Corollary 10.9: the assembly (Section 11.5)

Proposition 11.13 and the proofs of Theorem 10.8 and Corollary 10.9 in Section 11.5 (`zeroOne_of_T_mono`, `h2_gen`, the order of quantifiers),
including the special case of natural-number matrix interpretations (`zeroOne_liftNat`). Here `û`, `v̂` and `B_b` are $u$, $c$ and $N_b$ of Definition 10.1.
(Section 11.5.)

* **Core** (`gDiag_le_one_of_T_mono`; Proposition 11.13): for an automaton `L` all of whose indices are relevant, if the value `V(n) := aval L (bin'(n))` vanishes on multiples of 3
  (`h3`) and does not increase along steps of `T` from numbers `n ≥ 2` not divisible by 3 (`hT`), then `gDiag L.B ≤ 1`.
  By contradiction: if `G := gDiag L.B > 1`, then `lyap_compare` (Theorem 11.8) → `top_heavy` (Corollary 11.4; a heavy family of words, `a, Ψ, h, c`) →
  `rel_exists_words` (`p₀, s`) → `aval_poly_bound` (Corollary 11.2; `C`, `p = |Q|`) → `shrink_contra` (Proposition 11.12; shrinking chains and hitting a residue,
  `j' → ∞`). The order of quantifiers is "interpretation → `K` → `Ψ, h, a` → `p₀, s` → `j → ∞`", as in the written proof.
* **The form for general automata** (`zeroOne_of_T_mono`; Theorem 10.8): with `hT` and `h3` only, all components of `L` (strongly connected components of relevant indices
  with an internal edge) are 0/1. Pass to `L' := restrictRel L` (in the manner of `rel_restrictRel` and `lyap_compare_restrict`)
  and apply the core, bound the diagonal of a component by the diagonal of `L'` (`DxN_restrictRel_apply`, `diag_le_gDiag`), and apply
  `entry_bound` of Appendix D with `g = 1` (Lemma D.2).
* **Specializations** (Corollary 10.9): `h2_gen` (lifts of general families that weakly orient the 11 rules of $\mathcal T$), `zeroOne_liftNat`
  (the lift `liftNat I` of a natural-number matrix interpretation, in the form of the conclusion of `zeroOne_liftNat_of_h2Core` of `AutoCore.lean`), and the higher-level goal
  `h2Core : H2Core` (from `liftT_mono3`).
* **Assembly** (`natBarrierST_of_caseACore`, `natBarrierST_of_w3CoreStmt`): passing `h2Core` to `natBarrierST_of_W2_W3`,
  the only remaining hypothesis is `CaseACore` (or `W3CoreStmt`; Theorem 10.10, proved in Section 12).

Neither monotonicity (comparisons of the entries of `B_b`), nor inequalities between the matrices of rules, nor the homogeneous index of the underlying automaton, nor the diagonal at index 0 is used.
Auxiliary declarations are in the namespace `Collatz.Arctic.NatQ5.W2e`, the main theorems in `Collatz.Arctic.NatQ5`.
`sorry`, `axiom` and `native_decide` are not used.
-/
import CollatzProof.Arctic.Nat.H2Shrink
import CollatzProof.Arctic.Nat.H2Lyap2
import CollatzProof.Arctic.Nat.H2Path
import CollatzProof.Arctic.Nat.AutoCore

namespace Collatz.Arctic.NatQ5.W2e

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W2a Matrix

set_option linter.unusedSectionVars false

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- A lower bound for the values along the heavy family (the placement step of Section 11): if `(û B_{p₀})_a ≥ 1` and `(B_s v̂)_a ≥ 1`, then
`(B_ω)_{aa} ≤ V(p₀ ω s)` (real). -/
theorem Dx_le_aval (L : ValAuto Q) {p₀ s : List (Fin 2)} {a : Q}
    (hp : 1 ≤ (L.u ᵥ* Rigid.DxN L.B p₀) a) (hs : 1 ≤ (Rigid.DxN L.B s *ᵥ L.v) a) (ω : List (Fin 2)) :
    Rigid.Dx L.B ω a a ≤ (aval L (p₀ ++ ω ++ s) : ℝ) := by
  rw [Rigid.Dx_apply]
  have hpath := aval_ge_path L p₀ ω s a
  have : Rigid.DxN L.B ω a a ≤ aval L (p₀ ++ ω ++ s) := by
    refine le_trans ?_ hpath
    calc Rigid.DxN L.B ω a a = 1 * Rigid.DxN L.B ω a a * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_right _ hp) hs
  exact_mod_cast this

/-- The points of a component are relevant (`x ∈ sccOf L q` with `Rel L q`). -/
theorem rel_of_mem_sccOf (L : ValAuto Q) {q x : Q} (hq : Rel L q) (hx : x ∈ sccOf L q) : Rel L x := by
  obtain ⟨hqx, hxq⟩ := (mem_sccOf L).1 hx
  exact ⟨reach_of_conn L hq.1 hqx, coReach_of_conn L hq.2 hxq⟩

end Collatz.Arctic.NatQ5.W2e

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Collatz.Arctic.NatQ5.W2a Collatz.Arctic.NatQ5.W2e Matrix

set_option linter.unusedSectionVars false

/-! ## §1 The core: `gDiag ≤ 1` -/

section Core

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- **Core** (Proposition 11.13): for an automaton `L` all of whose indices are relevant, if the value `V(n) := aval L (bin'(n))`
does not increase along steps of `T` from numbers `n ≥ 2` not divisible by 3 (`hT`) and vanishes on multiples `n ≥ 1` of 3 (`h3`), then `gDiag L.B ≤ 1`. -/
theorem gDiag_le_one_of_T_mono (L : ValAuto Q) (hall : ∀ q, Rel L q)
    (hT : ∀ n, 2 ≤ n → ¬ 3 ∣ n → aval L (binWord (Collatz.Arctic.T n)) ≤ aval L (binWord n))
    (h3 : ∀ n, 1 ≤ n → 3 ∣ n → aval L (binWord n) = 0) :
    Rigid.gDiag L.B ≤ 1 := by
  by_contra hG
  push Not at hG
  -- Theorem 11.8 and Corollary 11.4: the heavy family of words
  obtain ⟨a, Ψ, h, c, hh, hc, hw⟩ :=
    top_heavy L hG (Rigid.diag_le_gDiag L.B) (lyap_compare L hall hT h3)
  -- The words before and after a path through `a`
  obtain ⟨p₀, s, hp, hs⟩ := rel_exists_words L (hall a)
  -- Corollary 11.2: the polynomial bound
  obtain ⟨C, -, hpoly⟩ := aval_poly_bound L hG.le (Rigid.diag_le_gDiag L.B)
  -- Proposition 11.12: contradiction by shrinking chains and hitting a residue
  refine shrink_contra (fun n => (aval L (binWord n) : ℝ)) Ψ p₀ s hh (C := C) (p := Fintype.card Q) hG hc
    ?_ ?_ ?_ ?_
  · intro n hn hn3; exact_mod_cast hT n hn hn3
  · intro n hn hn3; simp [h3 n hn hn3]
  · intro n _ _; exact hpoly (binWord n)
  · intro ε
    simp only [binWord_valW]
    exact (hw ε).trans (Dx_le_aval L hp hs _)

end Core

/-! ## §2 The form for general automata (Theorem 10.8) -/

section General

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The diagonal `g` of the restriction `restrictRel L` is at most 1 (transfer `hT` and `h3` by `aval_restrictRel` and apply the core; Theorem 10.8 (i)). -/
theorem gDiag_restrictRel_le_one (L : ValAuto Q)
    (hT : ∀ n, 2 ≤ n → ¬ 3 ∣ n → aval L (binWord (Collatz.Arctic.T n)) ≤ aval L (binWord n))
    (h3 : ∀ n, 1 ≤ n → 3 ∣ n → aval L (binWord n) = 0) :
    Rigid.gDiag (restrictRel L).B ≤ 1 :=
  gDiag_le_one_of_T_mono (restrictRel L) (W2c.rel_restrictRel L)
    (fun n hn hn3 => by rw [aval_restrictRel, aval_restrictRel]; exact hT n hn hn3)
    (fun n hn hn3 => by rw [aval_restrictRel]; exact h3 n hn hn3)

/-- **Theorem 10.8 (ii) (the form for general automata)**: if the value `V(n) := aval L (bin'(n))` does not increase along steps of `T` from numbers `n ≥ 2` not divisible by 3
(`hT`) and vanishes on multiples `n ≥ 1` of 3 (`h3`), then all components of `L` (strongly connected components of relevant indices with an internal edge) are 0/1. -/
theorem zeroOne_of_T_mono (L : ValAuto Q)
    (hT : ∀ n, 2 ≤ n → ¬ 3 ∣ n → aval L (binWord (Collatz.Arctic.T n)) ≤ aval L (binWord n))
    (h3 : ∀ n, 1 ≤ n → 3 ∣ n → aval L (binWord n) = 0) :
    ∀ C, IsComp L C → ZeroOne L C := by
  rintro C ⟨⟨q, hq, rfl⟩, -⟩
  have hG := gDiag_restrictRel_le_one L hT h3
  have hG0 := Rigid.gDiag_nonneg (restrictRel L).B
  -- The diagonal of a component is a diagonal of `restrictRel L`, hence at most `1^{|w|}`
  have hdiag : ∀ (w : List (Fin 2)) (i : sccOf L q),
      Rigid.Dx (compMat L (sccOf L q)) w i i ≤ (1 : ℝ) ^ w.length := by
    intro w i
    have hi : i.1 ∈ relSet L := (mem_relSet L).2 (rel_of_mem_sccOf L hq i.2)
    have e1 : Rigid.Dx (compMat L (sccOf L q)) w i i = Rigid.Dx (restrictRel L).B w ⟨i.1, hi⟩ ⟨i.1, hi⟩ := by
      rw [Rigid.Dx_apply, Rigid.Dx_apply, W2c.DxN_restrictRel_apply]
      exact_mod_cast DC_apply L q w i i
    rw [e1]
    exact (Rigid.diag_le_gDiag _ w _).trans (pow_le_pow_left₀ hG0 hG _)
  -- Lemma D.2 (`entry_bound` with `g = 1`)
  obtain ⟨L0, hL0⟩ := Rigid.entry_bound _ (sc_compMat L q) le_rfl hdiag
  intro w x y
  have h1 := hL0 w x y
  rw [one_pow, Rigid.Dx_apply] at h1
  exact_mod_cast h1

end General

/-! ## §3 Specializations (Corollary 10.9) and the higher-level goal -/

/-- The values of the lift vanish on multiples of 3 (`aval_liftT`). -/
theorem aval_liftT_three_dvd {Q : Type*} [Fintype Q] [DecidableEq Q] (A : ValAuto Q) :
    ∀ n, 1 ≤ n → 3 ∣ n → aval (liftT A) (binWord n) = 0 := by
  intro n hn hn3
  rw [aval_liftT A n hn]; simp [hn3]

/-- **The form for lifts** (Corollary 10.9 (1)): for an automaton `A` whose value does not increase along steps of `T` (`AutoMono`), all components of the lift `liftT A` are 0/1
(`H2Prod A`). -/
theorem h2Prod_of_autoMono {Q : Type*} [Fintype Q] [DecidableEq Q] {A : ValAuto Q} (hmono : AutoMono A) :
    H2Prod A :=
  zeroOne_of_T_mono (liftT A) (liftT_mono3 hmono) (aval_liftT_three_dvd A)

/-- **The higher-level goal** (`H2Core` of `AutoCore.lean`). -/
theorem h2Core : H2Core := fun _ _ _ _ hmono => h2Prod_of_autoMono hmono

/-- **The form for general families** (`h2_gen`, Corollary 10.9 (2)): for a family `N` that weakly orients all 11 rules of $\mathcal T$ (matrix index `ι`,
start `a`, end `z`), all components of the lift `liftT (genAuto N a z)` are 0/1. -/
theorem h2_gen {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Letter → Matrix ι ι ℕ) (a z : ι)
    (hw : ∀ ρ ∈ rulesST, GWeak N ρ) :
    ∀ C, IsComp (liftT (genAuto N a z)) C → ZeroOne (liftT (genAuto N a z)) C :=
  zeroOne_of_T_mono _ (fun _ hn hn3 => gavalT_T_le hw a z hn hn3) (aval_liftT_three_dvd _)

/-- **Natural-number matrix interpretations** (Corollary 10.9 (3)): for a natural-number matrix interpretation `I` that weakly orients all 11 rules of $\mathcal T$
(monotonicity is not used), all components of the lift `liftNat I` are 0/1. The form of the conclusion of `zeroOne_liftNat_of_h2Core`. -/
theorem zeroOne_liftNat {d : ℕ} [NeZero d] (I : Letter → NAff d) (hweak : ∀ ρ ∈ rulesST, NWeak I ρ) :
    ∀ C, IsComp (liftNat I) C → ZeroOne (liftNat I) C :=
  h2Prod_of_autoMono (natAuto_mono hweak)

/-- `zeroOne_liftNat` is the same as the form required in `AutoCore.lean` (`zeroOne_liftNat_of_h2Core`). -/
theorem zeroOne_liftNat_eq_of_h2Core : ∀ (d : ℕ) [NeZero d] (I : Letter → NAff d),
    (∀ ρ ∈ rulesST, NWeak I ρ) → ∀ C, IsComp (liftNat I) C → ZeroOne (liftNat I) C :=
  zeroOne_liftNat_of_h2Core h2Core

/-- (A^rel) (the remark after Corollary 10.9; a step of an earlier assembly of Theorem 9.2 (i)): the lift of a natural-number matrix interpretation satisfies (A^rel). -/
theorem aRel_liftNat {d : ℕ} [NeZero d] (I : Letter → NAff d) (hweak : ∀ ρ ∈ rulesST, NWeak I ρ) :
    ARel (liftNat I) :=
  aRel_of_zeroOne _ (zeroOne_liftNat I hweak)

/-! ## §4 Assembly: the only remaining hypothesis is that of Section 12 -/

/-- **The assembly without the hypothesis of Section 11**: passing `h2Core` to `natBarrierST_of_W2_W3`, the only remaining hypothesis is `CaseACore` (Section 12). -/
theorem natBarrierST_of_caseACore (h3 : CaseACore) : NatBarrierST ∧ NatBarrierSTB ∧ GenValueCore :=
  natBarrierST_of_W2_W3 h2Core h3

/-- The form from the statement `W3CoreStmt` (Theorem 10.10). -/
theorem natBarrierST_of_w3CoreStmt (h3 : W3CoreStmt) : NatBarrierST ∧ NatBarrierSTB ∧ GenValueCore :=
  natBarrierST_of_caseACore (caseACore_of_w3CoreStmt h3)

end Collatz.Arctic.NatQ5
