/-
# Natural-number matrix interpretations ($\mathcal T$): non-vacuity checks for Theorem 11.8 of the paper

The premises of `lyap_compare` (`H2Lyap.lean`; Theorem 11.8 of the paper) can be satisfied, and none of the three hypotheses `hall`, `hT`, `h3` can be dropped. Outside the
closure of the main theorems. The entries and sums of matrices are computed by `decide +kernel`.

* §2 (a) **The premises can be satisfied**: in `liftT (auto1 1 1)` (value `[3 ∤ n]`, the example of `NonVacuityW1.lean`) all indices are relevant, and `hT`, `h3` hold.
  `lyap_compare` applies (`exA_concl`). For automata that satisfy the premises one expects `G ≤ 1` (the conclusion of Proposition 11.13 of the paper), so
  the conclusion is effective only in the proof by contradiction (the case `1 < G`). What is checked here is that the premises are consistent.
* §3 (b) **`hall` cannot be dropped** (internal independent review): the lift `liftT exIrr` of a two-state automaton with a heavy self-loop (`(B_0)_{11} = 4`)
  at the irrelevant index 1. It satisfies `hT` and `h3`, `G ≥ 4` and `bAvg_2 = (log 51 + 3 log 3)/4 < 2 log 4`, so the conclusion is false
  (`exIrr_fails`). Hence, by `lyap_compare`, there is an irrelevant index (`exIrr_not_hall`).
* §4 (c) **`hT` cannot be dropped**: in `liftT (auto1 4 1)` (value `4^{#0(bin'(n))} [3 ∤ n]`) all indices are relevant and `h3` holds, but
  `G ≥ 4` and `bAvg_2 = log(48·12·12·3)/4 < 2 log 4`, so the conclusion is false (`ex41_fails`). By `lyap_compare`, `hT` fails
  (`ex41_not_hT`; directly, `T 5 = 8` and `V(8) = 64 > 4 = V(5)`).
* §5 (d) **`h3` cannot be dropped**: `lift (auto1 4 1) 3 {0}` (value `4^{#0} [3 ∣ n]`), with the same digit matrices and the exit at the residue 0,
  has all indices relevant and satisfies `hT` (the value is 0 on the numbers not divisible by 3), but the conclusion is false for the same reason as in (c) (`ex41z_fails`).
  By `lyap_compare`, `h3` fails (`ex41z_not_h3`; directly, `V(3) = 1`).
-/
import CollatzProof.Arctic.Nat.H2Lyap2
import CollatzProof.Arctic.Nat.NonVacuityW1

namespace Collatz.Arctic.NatQ5.W2c

open Collatz.Arctic Collatz.Arctic.NatQ5 Matrix

set_option linter.unusedSectionVars false

/-! ## §1 Predicates and general lemmas -/

section General

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The hypothesis `hT` of `lyap_compare`. -/
def HypT (L : ValAuto Q) : Prop :=
  ∀ n, 2 ≤ n → ¬ 3 ∣ n → aval L (binWord (Collatz.Arctic.T n)) ≤ aval L (binWord n)

/-- The hypothesis `h3` of `lyap_compare`. -/
def Hyp3 (L : ValAuto Q) : Prop := ∀ n, 1 ≤ n → 3 ∣ n → aval L (binWord n) = 0

/-- The conclusion of `lyap_compare`. -/
def LyapConcl (L : ValAuto Q) : Prop :=
  ∀ κ : ℕ, 1 ≤ κ → (κ : ℝ) * Real.log (Rigid.gDiag L.B) ≤ Rigid.bAvg L.B κ

/-- `lyap_compare` in the form with these predicates. -/
theorem lyapConcl_of (L : ValAuto Q) (hall : ∀ q, Rel L q) (hT : HypT L) (h3 : Hyp3 L) : LyapConcl L :=
  lyap_compare L hall hT h3

theorem rel_of_words (A : ValAuto Q) {i j q : Q} (hu : 1 ≤ A.u i) (w : List (Fin 2))
    (hw : 1 ≤ Rigid.DxN A.B w i q) (w' : List (Fin 2)) (hw' : 1 ≤ Rigid.DxN A.B w' q j) (hv : 1 ≤ A.v j) :
    Rel A q :=
  ⟨⟨i, hu, w, hw⟩, ⟨j, ⟨w', hw'⟩, hv⟩⟩

theorem nrm_Dx_eq_sum (B : Fin 2 → Matrix Q Q ℕ) (x : List (Fin 2)) :
    Rigid.nrm (Rigid.Dx B x) = ((∑ i, ∑ j, Rigid.DxN B x i j : ℕ) : ℝ) := by
  rw [Rigid.nrm_of_nonneg (Rigid.Dx_nonneg B x)]
  push_cast
  simp only [Rigid.Dx_apply]

theorem flog_eq_log (B : Fin 2 → Matrix Q Q ℕ) (x : List (Fin 2)) {s : ℕ}
    (h : ∑ i, ∑ j, Rigid.DxN B x i j = s) : flog B x = Real.log s := by
  rw [flog, nrm_Dx_eq_sum, h, Real.log_of_nat_eq_posLog]

theorem bAvg_two (B : Fin 2 → Matrix Q Q ℕ) :
    Rigid.bAvg B 2 = (flog B [0, 0] + flog B [0, 1] + flog B [1, 0] + flog B [1, 1]) / 4 := by
  rw [Rigid.bAvg_eq_wsum]
  simp only [Rigid.wsum, Fin.sum_univ_two]
  unfold flog
  ring

/-- A lower bound for `gDiag` from a diagonal entry. -/
theorem four_le_gDiag (B : Fin 2 → Matrix Q Q ℕ) (i : Q) (h : Rigid.DxN B [0, 0] i i = 16) :
    (4 : ℝ) ≤ Rigid.gDiag B := by
  have hle := le_ciSup (Rigid.bddAbove_gDiag B) (⟨⟨[0, 0], by simp⟩, i⟩ : {w : List (Fin 2) // w ≠ []} × Q)
  have e1 : Rigid.Dx B [0, 0] i i = (4 : ℝ) ^ 2 := by rw [Rigid.Dx_apply, h]; norm_num
  have e2 : ((([0, 0] : List (Fin 2)).length : ℕ) : ℝ) = ((2 : ℕ) : ℝ) := rfl
  simp only at hle
  rw [e1, e2, Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)] at hle
  exact hle

/-- A test for the failure of the conclusion at `κ = 2`: `G ≥ 4` and `bAvg_2 < 2 log 4`. -/
theorem not_concl_of (L : ValAuto Q) (h4 : (4 : ℝ) ≤ Rigid.gDiag L.B)
    (hb : Rigid.bAvg L.B 2 < 2 * Real.log 4) : ¬ LyapConcl L := by
  intro h
  have h2 := h 2 (by norm_num)
  have hlog : Real.log 4 ≤ Real.log (Rigid.gDiag L.B) := Real.log_le_log (by norm_num) h4
  push_cast at h2
  linarith

theorem log_lt_mul_log4 {x : ℝ} (n : ℕ) (hx : 0 < x) (h : x < 4 ^ n) : Real.log x < n * Real.log 4 := by
  rw [← Real.log_pow]
  exact Real.log_lt_log hx h

/-- The elements of `ZMod 3` are 0, 1, 2. -/
theorem zmod3_cases (r : ZMod 3) : r = 0 ∨ r = 1 ∨ r = 2 := by
  revert r; decide

end General

/-! ## §2 (a) The premises can be satisfied: `liftT (auto1 1 1)` -/

theorem exA_hall : ∀ q, Rel (liftT (auto1 1 1)) q := by
  rintro ⟨⟨⟩, r⟩
  rcases zmod3_cases r with rfl | rfl | rfl
  · exact rel_of_words _ (i := ((), 1)) (j := ((), 1)) (by decide) [1] (by decide +kernel) [1]
      (by decide +kernel) (by decide)
  · exact rel_of_words _ (i := ((), 1)) (j := ((), 1)) (by decide) [] (by decide +kernel) []
      (by decide +kernel) (by decide)
  · exact rel_of_words _ (i := ((), 1)) (j := ((), 2)) (by decide) [0] (by decide +kernel) []
      (by decide +kernel) (by decide)

theorem exA_hT : HypT (liftT (auto1 1 1)) := autoMono3_liftT_A1

theorem exA_h3 : Hyp3 (liftT (auto1 1 1)) := fun n hn h => by
  rw [aval_liftT_auto1 n hn]; simp [h]

/-- (a) All premises can be satisfied, and `lyap_compare` applies. -/
theorem exA_concl : LyapConcl (liftT (auto1 1 1)) := lyapConcl_of _ exA_hall exA_hT exA_h3

/-! ## §3 (b) `hall` cannot be dropped: a heavy self-loop at an irrelevant index -/

/-- Index 0 is relevant (`(B_b)_{00} = 1`). Index 1 is cut off from the start and from the exit, and `(B_0)_{11} = 4`. -/
def exIrr : ValAuto (Fin 2) where
  B b := fun i j => if i = 0 ∧ j = 0 then 1 else if i = 1 ∧ j = 1 ∧ b = 0 then 4 else 0
  u i := if i = 0 then 1 else 0
  v i := if i = 0 then 1 else 0

theorem exIrr_DxN_zero_row (ω : List (Fin 2)) (j : Fin 2) :
    Rigid.DxN exIrr.B ω 0 j = if j = 0 then 1 else 0 := by
  induction ω with
  | nil => fin_cases j <;> rfl
  | cons b ω ih =>
    rw [DxN_apply_cons, Fin.sum_univ_two, ih]
    fin_cases j <;> simp [exIrr]

theorem exIrr_aval (ω : List (Fin 2)) : aval exIrr ω = 1 := by
  rw [aval_eq_sum, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, exIrr_DxN_zero_row,
    exIrr_DxN_zero_row]
  simp [exIrr]

theorem exIrr_hT : HypT (liftT exIrr) :=
  liftT_mono3 fun n _ => by rw [exIrr_aval, exIrr_aval]

theorem exIrr_h3 : Hyp3 (liftT exIrr) := fun n hn h => by
  rw [aval_liftT _ n hn]; simp [h]

theorem exIrr_fails : ¬ LyapConcl (liftT exIrr) := by
  refine not_concl_of _ (four_le_gDiag _ ((1 : Fin 2), (0 : ZMod 3)) (by decide +kernel)) ?_
  rw [bAvg_two, flog_eq_log _ [0, 0] (s := 51) (by decide +kernel), flog_eq_log _ [0, 1] (s := 3) (by decide +kernel),
    flog_eq_log _ [1, 0] (s := 3) (by decide +kernel), flog_eq_log _ [1, 1] (s := 3) (by decide +kernel)]
  have h1 := log_lt_mul_log4 3 (x := ((51 : ℕ) : ℝ)) (by norm_num) (by norm_num)
  have h2 := log_lt_mul_log4 1 (x := ((3 : ℕ) : ℝ)) (by norm_num) (by norm_num)
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  push_cast at h1 h2
  linarith

/-- (b) `hT` and `h3` hold and the conclusion is false, so by `lyap_compare` there is an irrelevant index (`hall` cannot be dropped). -/
theorem exIrr_not_hall : ¬ ∀ q, Rel (liftT exIrr) q := fun hall =>
  exIrr_fails (lyapConcl_of _ hall exIrr_hT exIrr_h3)

/-! ## §4 (c) `hT` cannot be dropped: `liftT (auto1 4 1)` -/

theorem ex41_hall : ∀ q, Rel (liftT (auto1 4 1)) q := by
  rintro ⟨⟨⟩, r⟩
  rcases zmod3_cases r with rfl | rfl | rfl
  · exact rel_of_words _ (i := ((), 1)) (j := ((), 1)) (by decide) [1] (by decide +kernel) [1]
      (by decide +kernel) (by decide)
  · exact rel_of_words _ (i := ((), 1)) (j := ((), 1)) (by decide) [] (by decide +kernel) []
      (by decide +kernel) (by decide)
  · exact rel_of_words _ (i := ((), 1)) (j := ((), 2)) (by decide) [0] (by decide +kernel) []
      (by decide +kernel) (by decide)

theorem ex41_h3 : Hyp3 (liftT (auto1 4 1)) := fun n hn h => by
  rw [aval_liftT _ n hn]; simp [h]

/-- With the digit matrices `liftB (auto1 4 1) 3` the conclusion fails at `κ = 2`. -/
theorem ex41_fails : ¬ LyapConcl (liftT (auto1 4 1)) := by
  refine not_concl_of _ (four_le_gDiag _ ((), (0 : ZMod 3)) (by decide +kernel)) ?_
  rw [bAvg_two, flog_eq_log _ [0, 0] (s := 48) (by decide +kernel), flog_eq_log _ [0, 1] (s := 12) (by decide +kernel),
    flog_eq_log _ [1, 0] (s := 12) (by decide +kernel), flog_eq_log _ [1, 1] (s := 3) (by decide +kernel)]
  have h1 := log_lt_mul_log4 3 (x := ((48 : ℕ) : ℝ)) (by norm_num) (by norm_num)
  have h2 := log_lt_mul_log4 2 (x := ((12 : ℕ) : ℝ)) (by norm_num) (by norm_num)
  have h3 := log_lt_mul_log4 1 (x := ((3 : ℕ) : ℝ)) (by norm_num) (by norm_num)
  push_cast at h1 h2 h3
  linarith

/-- The conclusion depends only on the digit matrices, so it fails whatever the set of exits is. -/
theorem ex41_fails_B (Pc : Finset (ZMod 3)) : ¬ LyapConcl (lift (auto1 4 1) 3 Pc) := by
  have e : (lift (auto1 4 1) 3 Pc).B = (liftT (auto1 4 1)).B := rfl
  unfold LyapConcl
  rw [e]
  exact ex41_fails

/-- (c) All indices are relevant, `h3` holds and the conclusion is false, so by `lyap_compare` `hT` fails. -/
theorem ex41_not_hT : ¬ HypT (liftT (auto1 4 1)) := fun hT =>
  ex41_fails (lyapConcl_of _ ex41_hall hT ex41_h3)

/-- A direct check: `T 5 = 8`, `V(5) = 4 < 64 = V(8)`. -/
theorem ex41_direct : Collatz.Arctic.T 5 = 8 ∧ aval (liftT (auto1 4 1)) (binWord 5) = 4 ∧
    aval (liftT (auto1 4 1)) (binWord 8) = 64 := by
  decide +kernel

/-! ## §5 (d) `h3` cannot be dropped: `lift (auto1 4 1) 3 {0}` -/

theorem ex41z_hall : ∀ q, Rel (lift (auto1 4 1) 3 {0}) q := by
  rintro ⟨⟨⟩, r⟩
  rcases zmod3_cases r with rfl | rfl | rfl
  · exact rel_of_words _ (i := ((), 1)) (j := ((), 0)) (by decide) [1] (by decide +kernel) []
      (by decide +kernel) (by decide)
  · exact rel_of_words _ (i := ((), 1)) (j := ((), 0)) (by decide) [] (by decide +kernel) [1]
      (by decide +kernel) (by decide)
  · exact rel_of_words _ (i := ((), 1)) (j := ((), 0)) (by decide) [0] (by decide +kernel) [0, 1]
      (by decide +kernel) (by decide)

/-- The value is 0 on the numbers not divisible by 3, so `hT` holds trivially. -/
theorem ex41z_hT : HypT (lift (auto1 4 1) 3 {0}) := by
  intro n hn hn3
  have hTn : ¬ 3 ∣ Collatz.Arctic.T n := fun h => hn3 (three_dvd_of_three_dvd_T h)
  have h0 : aval (lift (auto1 4 1) 3 {0}) (binWord (Collatz.Arctic.T n)) = 0 := by
    rw [aval_lift, valW_binWord _ (one_le_T hn)]
    have : ((Collatz.Arctic.T n : ℕ) : ZMod 3) ≠ 0 := fun h => hTn ((ZMod.natCast_eq_zero_iff _ 3).1 h)
    simp [this]
  rw [h0]
  exact Nat.zero_le _

theorem ex41z_fails : ¬ LyapConcl (lift (auto1 4 1) 3 {0}) := ex41_fails_B {0}

/-- (d) All indices are relevant, `hT` holds and the conclusion is false, so by `lyap_compare` `h3` fails. -/
theorem ex41z_not_h3 : ¬ Hyp3 (lift (auto1 4 1) 3 {0}) := fun h3 =>
  ex41z_fails (lyapConcl_of _ ex41z_hall ex41z_hT h3)

/-- A direct check: `V(3) = 1` (non-zero at a multiple of 3). -/
theorem ex41z_direct : aval (lift (auto1 4 1) 3 {0}) (binWord 3) = 1 := by decide +kernel

end Collatz.Arctic.NatQ5.W2c
