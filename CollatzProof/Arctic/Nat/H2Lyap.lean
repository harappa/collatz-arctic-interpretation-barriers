/-
# Theorem 11.8: the diagonal form of the Lyapunov comparison

Theorem 11.8 (diagonal Lyapunov comparison), in the form that `top_rigid` (`H2Top.lean`, Lemma 11.3) receives as the hypothesis `hLC`.
(Section 11.3.)


**Main theorem** `lyap_compare`: if every index of the value automaton `L` is relevant (`hall`), and the value `V(n) := aval L (bin'(n))`
does not increase along steps of `T` from numbers `n ≥ 2` not divisible by 3 (`hT`) and vanishes on multiples of 3 (`h3`), then for all `κ ≥ 1`
\[
  \kappa\log G \le \mathrm{bAvg}_\kappa := 2^{-\kappa}\sum_{\lvert x\rvert = \kappa}\log^+\lVert B_x\rVert ,
  \qquad G := \mathrm{gDiag}(B) = \sup_{w \ne [],\,i}\bigl((B_w)_{ii}\bigr)^{1/\lvert w\rvert} .
\]

**Proof** (cf. the proof of Theorem 11.8): fix a diagonal word `w` (`L := |w| ≥ 1`), an index `ζ` and `d := (B_w)_{ζζ} ≥ 1`.
1. By `hall`, `ζ` is relevant, so there are a word `p` from the start to `ζ` and a word `s` from `ζ` to the exit (`rel_exists_words`).
2. Powers: `(B_{w^m})_{ζζ} ≥ d^m` (`pow_diag_le_wpow`). Perron–Frobenius is not used.
3. Pumping (Lemma 11.6): the pumping word is `w` itself. `A > b_0 := v_3((2^L - 1) val(1p) + val(w))`, `k := 2A` (`three_pow_le_valW_wpow`).
   By `back_chain_word`, the reduced fraction `N/D` (`D = 3^α D''`, `α ≥ A - b_0`, `D'' ∣ 2^L - 1`) is fixed before `m` is chosen.
4. For each `m`, `y_m := val(1 p w^k w^m s)`. The lower bound `V(y_m) ≥ d^{k+m} ≥ 1` (`aval_ge_path`) and `h3` give `3 ∤ y_m`.
   Applying `hT` repeatedly from the starting point `n` of the chain (`aval_iterate_le`, `not_three_dvd_iterate`) gives `V(y_m) ≤ V(n)`.
5. Upper bound: `bin'(n) = τ ++ dig N D 0 (Lm) ++ β`, where `τ` does not depend on `m` and `|β| ≤ |s| + 4A`. As `log⁺ ‖B_·‖` is subadditive
   (`flog_append`), split into aligned segments by `dig_zero_blocks` and apply `win_freq` with `f = log⁺ ‖B_x‖`:
   `(k + m) log d ≤ C_A + (Lm/κ + P_A)(2^{-κ} + 3^{c-α}) 2^κ bAvg_κ` (inside `chain_bound`).
6. **First take `m → ∞`** (`P_A = 2L·3^{α-c}` is exponentially large in `A`, so the limits must be taken in this order):
   `κ log d ≤ L (2^{-κ} + 3^{c-α}) 2^κ bAvg_κ` (`chain_bound`). Only a comparison of linear growth is used, not the existence of a limit
   (`le_of_forall_nat_mul_le`).
7. **Then `A → ∞`**: `3^{c-α} ≤ 3^{c + b_0}/3^A → 0` gives `κ log d ≤ L bAvg_κ` (`diag_log_le`).
8. Take the supremum over `(w, ζ)` and pass to `gDiag` (`lyap_compare`, `Real.iSup_le`).

**The case 1 of an earlier argument (some word `z` with `B_z = 0`) is not needed**: `bAvg` is an average of `log⁺`, and the upper bounds are all written with `log⁺`, so
the bounds hold as they are even if `B_x = 0` for some word (confirming an earlier expectation). Fekete's lemma (subadditivity of `ã_κ` and
existence of `\tilde Λ`), Perron–Frobenius, an earlier pumping lemma and the arithmetic progression `\mathfrak M` of the earlier argument are not used either.

Auxiliary declarations are in the namespace `Collatz.Arctic.NatQ5.W2c`, the main theorem `lyap_compare` in `Collatz.Arctic.NatQ5`.
`sorry`, `axiom` and `native_decide` are not used.
-/
import CollatzProof.Arctic.Nat.H2Chain
import CollatzProof.Arctic.Nat.H2Orbit
import CollatzProof.Arctic.Nat.RigidLower

namespace Collatz.Arctic.NatQ5.W2c

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W2a Matrix

set_option linter.unusedSectionVars false

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-! ## §1 Subadditivity of `log⁺ ‖B_x‖` -/

/-- `f(x) := log⁺ ‖B_x‖` (the integrand of `bAvg`). -/
noncomputable def flog (B : Fin 2 → Matrix Q Q ℕ) (x : List (Fin 2)) : ℝ :=
  Real.posLog (Rigid.nrm (Rigid.Dx B x))

theorem flog_nonneg (B : Fin 2 → Matrix Q Q ℕ) (x : List (Fin 2)) : 0 ≤ flog B x := Real.posLog_nonneg

/-- Subadditivity: `log⁺ ‖B_{xy}‖ ≤ log⁺ ‖B_x‖ + log⁺ ‖B_y‖`. -/
theorem flog_append (B : Fin 2 → Matrix Q Q ℕ) (x y : List (Fin 2)) :
    flog B (x ++ y) ≤ flog B x + flog B y := by
  unfold flog
  rw [Rigid.Dx_append]
  have h0 : (-1 : ℝ) ≤ Rigid.nrm (Rigid.Dx B x * Rigid.Dx B y) := by
    linarith [Rigid.nrm_nonneg (Rigid.Dx B x * Rigid.Dx B y)]
  calc Real.posLog (Rigid.nrm (Rigid.Dx B x * Rigid.Dx B y))
      ≤ Real.posLog (Rigid.nrm (Rigid.Dx B x) * Rigid.nrm (Rigid.Dx B y)) :=
        Real.posLog_le_posLog h0 (Rigid.nrm_mul_le _ _)
    _ ≤ _ := Real.posLog_mul

theorem flog_nil (B : Fin 2 → Matrix Q Q ℕ) : flog B [] = Real.posLog (Fintype.card Q) := by
  simp [flog, Rigid.nrm_one]

/-- The bound by the length: `log⁺ ‖B_x‖ ≤ log⁺ |Q| + |x| log W` (`W := max(1, ‖B_0‖, ‖B_1‖)`). -/
theorem flog_le_length (B : Fin 2 → Matrix Q Q ℕ) (x : List (Fin 2)) :
    flog B x ≤ Real.posLog (Fintype.card Q) + x.length * Real.log (Rigid.Wd B) := by
  have hW1 : 1 ≤ Rigid.Wd B := Rigid.one_le_Wd B
  have hlogW : 0 ≤ Real.log (Rigid.Wd B) := Real.log_nonneg hW1
  cases x with
  | nil => simp [flog_nil]
  | cons b x =>
    have h := Rigid.nrm_Dx_cons_le B b x
    have h0 : (-1 : ℝ) ≤ Rigid.nrm (Rigid.Dx B (b :: x)) := by
      linarith [Rigid.nrm_nonneg (Rigid.Dx B (b :: x))]
    have hpW : Real.posLog (Rigid.Wd B) = Real.log (Rigid.Wd B) :=
      Real.posLog_eq_log (by rw [abs_of_pos (by linarith)]; exact hW1)
    calc flog B (b :: x) ≤ Real.posLog (Rigid.Wd B ^ (x.length + 1)) := Real.posLog_le_posLog h0 h
      _ = ((b :: x).length : ℝ) * Real.log (Rigid.Wd B) := by
          rw [Real.posLog_pow, hpW]; simp
      _ ≤ _ := le_add_of_nonneg_left Real.posLog_nonneg

/-- The bound for concatenated words: `log⁺ ‖B_{g_0 ⋯ g_{q-1}}‖ ≤ log⁺ |Q| + Σ_{i<q} log⁺ ‖B_{g_i}‖`. -/
theorem flog_flatten_range (B : Fin 2 → Matrix Q Q ℕ) (g : ℕ → List (Fin 2)) (q : ℕ) :
    flog B ((List.range q).map g).flatten ≤ Real.posLog (Fintype.card Q) + ∑ i ∈ Finset.range q, flog B (g i) := by
  induction q with
  | zero => simp [flog_nil]
  | succ q ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, List.map_singleton, List.flatten_singleton,
      Finset.sum_range_succ]
    have := flog_append B (((List.range q).map g).flatten) (g q)
    linarith

/-- `wsum κ (log⁺ ‖B_·‖) = 2^κ bAvg_κ`. -/
theorem wsum_flog (B : Fin 2 → Matrix Q Q ℕ) (κ : ℕ) :
    Rigid.wsum κ (flog B) = 2 ^ κ * Rigid.bAvg B κ := by
  rw [Rigid.bAvg_eq_wsum, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero), one_mul]
  rfl

theorem bAvg_nonneg (B : Fin 2 → Matrix Q Q ℕ) (κ : ℕ) : 0 ≤ Rigid.bAvg B κ := by
  unfold Rigid.bAvg
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg)

/-! ## §2 Upper and lower bounds for the value -/

/-- An upper bound for the value: `V(ω) ≤ (Σ_i u_i)(Σ_j v_j) ‖B_ω‖`. -/
theorem aval_le_nrm (A : ValAuto Q) (ω : List (Fin 2)) :
    (aval A ω : ℝ) ≤ (∑ i, (A.u i : ℝ)) * (∑ j, (A.v j : ℝ)) * Rigid.nrm (Rigid.Dx A.B ω) := by
  set cU := ∑ i, (A.u i : ℝ) with hcU
  set cV := ∑ j, (A.v j : ℝ) with hcV
  have hu : ∀ i, (A.u i : ℝ) ≤ cU := fun i =>
    Finset.single_le_sum (f := fun i => (A.u i : ℝ)) (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ i)
  have hv : ∀ j, (A.v j : ℝ) ≤ cV := fun j =>
    Finset.single_le_sum (f := fun j => (A.v j : ℝ)) (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ j)
  have hcU0 : 0 ≤ cU := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hcV0 : 0 ≤ cV := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  rw [aval_eq_sum, Rigid.nrm_of_nonneg (Rigid.Dx_nonneg A.B ω)]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Rigid.Dx_apply]
  have hD : (0 : ℝ) ≤ (Rigid.DxN A.B ω i j : ℝ) := Nat.cast_nonneg _
  have huv : (A.u i : ℝ) * (A.v j : ℝ) ≤ cU * cV :=
    mul_le_mul (hu i) (hv j) (Nat.cast_nonneg _) hcU0
  calc (A.u i : ℝ) * (Rigid.DxN A.B ω i j : ℝ) * (A.v j : ℝ)
      = ((A.u i : ℝ) * (A.v j : ℝ)) * (Rigid.DxN A.B ω i j : ℝ) := by ring
    _ ≤ (cU * cV) * (Rigid.DxN A.B ω i j : ℝ) := mul_le_mul_of_nonneg_right huv hD

/-- The upper bound for the value in the form of `log⁺`. -/
theorem posLog_aval_le (A : ValAuto Q) (ω : List (Fin 2)) :
    Real.posLog (aval A ω : ℝ) ≤
      Real.posLog ((∑ i, (A.u i : ℝ)) * (∑ j, (A.v j : ℝ))) + flog A.B ω := by
  have h0 : (-1 : ℝ) ≤ (aval A ω : ℝ) := by linarith [(Nat.cast_nonneg (aval A ω) : (0 : ℝ) ≤ _)]
  exact (Real.posLog_le_posLog h0 (aval_le_nrm A ω)).trans Real.posLog_mul

/-- `w^{k+m} = w^k w^m`. -/
theorem wpow_add (w : List (Fin 2)) (k m : ℕ) : wpow w (k + m) = wpow w k ++ wpow w m := by
  unfold wpow
  rw [List.replicate_add, List.flatten_append]

/-- **Powers** (Step 2): the lower bound for diagonal powers `(B_{w^m})_{ζζ} ≥ ((B_w)_{ζζ})^m` (instead of Perron–Frobenius). -/
theorem pow_diag_le_wpow (B : Fin 2 → Matrix Q Q ℕ) (w : List (Fin 2)) (ζ : Q) (m : ℕ) :
    Rigid.DxN B w ζ ζ ^ m ≤ Rigid.DxN B (wpow w m) ζ ζ := by
  induction m with
  | zero => simp [wpow_zero]
  | succ m ih =>
    rw [wpow_succ, pow_succ]
    exact (Nat.mul_le_mul_right _ ih).trans (le_DxN_append B _ _ ζ ζ ζ)

/-- On a segment of an orbit (all points at least 2, the starting point not divisible by 3) the value does not increase (`hT` applied repeatedly). -/
theorem aval_iterate_le (L : ValAuto Q)
    (hT : ∀ n, 2 ≤ n → ¬ 3 ∣ n → aval L (binWord (Collatz.Arctic.T n)) ≤ aval L (binWord n)) :
    ∀ (M n : ℕ), ¬ 3 ∣ n → (∀ i < M, 2 ≤ Collatz.Arctic.T^[i] n) →
      aval L (binWord (Collatz.Arctic.T^[M] n)) ≤ aval L (binWord n) := by
  intro M
  induction M with
  | zero => intro n _ _; simp
  | succ M ih =>
    intro n hn3 horb
    have hn : 2 ≤ n := by simpa using horb 0 (Nat.succ_pos M)
    have horb' : ∀ i < M, 2 ≤ Collatz.Arctic.T^[i] (Collatz.Arctic.T n) := by
      intro i hi
      have := horb (i + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    have hT3 : ¬ 3 ∣ Collatz.Arctic.T n := by
      have := not_three_dvd_iterate hn3 1
      simpa using this
    rw [Function.iterate_succ_apply]
    exact (ih (Collatz.Arctic.T n) hT3 horb').trans (hT n hn hn3)

/-! ## §3 An elementary lemma on limits -/

/-- Comparison of linear growth: if `m a ≤ b` for all `m`, then `a ≤ 0`. -/
theorem le_of_forall_nat_mul_le {a b : ℝ} (h : ∀ m : ℕ, (m : ℝ) * a ≤ b) : a ≤ 0 := by
  by_contra ha
  push Not at ha
  obtain ⟨m, hm⟩ := exists_nat_gt (b / a)
  have h1 := h m
  have h2 : b < (m : ℝ) * a := by
    rw [div_lt_iff₀ ha] at hm
    exact hm
  linarith

/-! ## §4 The bound at one depth `A` (`m → ∞`) -/

/-- **The bound at one depth `A`** (the steps "placement" and "chains" and the step `m → ∞` of the proof of Theorem 11.8, Steps 1–7):
if `(B_w)_{ζζ} ≥ 1`, `p` is a word reaching `ζ`, `s` a word from `ζ` to the exit and `A > b_0`, then, for the power `α ≥ A - b_0` of 3 in the denominator of `back_chain_word`,
we have
\[
  \kappa\log (B_w)_{\zeta\zeta} \le L\,(2^{-\kappa} + 3^{c-\alpha})\sum_{\lvert x\rvert=\kappa}\log^+\lVert B_x\rVert ,
  \qquad c = 1 + v_3(\kappa L),\ L = \lvert w\rvert .
\]
The pumping exponent is `k = 2A`, and `N/D` is fixed before `m` is chosen. The additive term `P = 2L·3^{α-c}` and the contributions of the words `τ`, `β` before and after
do not depend on `m`, so they disappear in the comparison of linear growth in `m` (`le_of_forall_nat_mul_le`). -/
theorem chain_bound (L : ValAuto Q)
    (hT : ∀ n, 2 ≤ n → ¬ 3 ∣ n → aval L (binWord (Collatz.Arctic.T n)) ≤ aval L (binWord n))
    (h3 : ∀ n, 1 ≤ n → 3 ∣ n → aval L (binWord n) = 0)
    {w p s : List (Fin 2)} (hw : 1 ≤ w.length) {ζ : Q}
    (hp : 1 ≤ (L.u ᵥ* Rigid.DxN L.B p) ζ) (hs : 1 ≤ (Rigid.DxN L.B s *ᵥ L.v) ζ)
    (hd : 1 ≤ Rigid.DxN L.B w ζ ζ) {κ A : ℕ} (hκ : 1 ≤ κ)
    (hA : padicValNat 3 ((2 ^ w.length - 1) * valW 1 p + valW 0 w) < A) :
    ∃ α : ℕ, A - padicValNat 3 ((2 ^ w.length - 1) * valW 1 p + valW 0 w) ≤ α ∧
      (κ : ℝ) * Real.log (Rigid.DxN L.B w ζ ζ : ℝ) ≤
        w.length * ((((2 : ℝ) ^ κ)⁻¹ + (3 : ℝ) ^ (((1 + padicValNat 3 (κ * w.length) : ℕ) : ℤ) - α)) *
          Rigid.wsum κ (flog L.B)) := by
  have hU := three_pow_le_valW_wpow p w A hw
  obtain ⟨N, D, α, D'', hcop, hN0, hND, hDsplit, hD''3, hD''R, hαge, hch⟩ :=
    back_chain_word p w s (2 * A) A hw hU hA
  refine ⟨α, hαge, ?_⟩
  have hD : 0 < D := lt_trans hN0 hND
  -- Frequencies of segments (Lemma 11.7), taken first in a form independent of `m`
  have hwin : ∀ q : ℕ, ∑ i ∈ Finset.range q, flog L.B (dig N D (κ * i) κ) ≤
      ((q : ℝ) + 2 * w.length * 3 ^ (α - (1 + padicValNat 3 (κ * w.length)))) *
        (((2 : ℝ) ^ κ)⁻¹ + (3 : ℝ) ^ (((1 + padicValNat 3 (κ * w.length) : ℕ) : ℤ) - α)) *
          Rigid.wsum κ (flog L.B) :=
    fun q => win_freq hcop hDsplit hD''3 hD''R hw hκ (flog L.B) (fun x _ => flog_nonneg _ x) q
  have hE0 : (0 : ℝ) ≤ ((2 : ℝ) ^ κ)⁻¹ + (3 : ℝ) ^ (((1 + padicValNat 3 (κ * w.length) : ℕ) : ℤ) - α) := by
    positivity
  have hWf0 : (0 : ℝ) ≤ Rigid.wsum κ (flog L.B) := Rigid.wsum_nonneg fun x _ => flog_nonneg _ x
  generalize (((2 : ℝ) ^ κ)⁻¹ + (3 : ℝ) ^ (((1 + padicValNat 3 (κ * w.length) : ℕ) : ℤ) - α)) = E
    at hwin hE0 ⊢
  generalize Rigid.wsum κ (flog L.B) = Wf at hwin hWf0 ⊢
  generalize (2 : ℝ) * w.length * 3 ^ (α - (1 + padicValNat 3 (κ * w.length))) = P at hwin
  -- Constants independent of `m`
  obtain ⟨τ, hτ⟩ : ∃ τ, binWord (valW 1 (p ++ wpow w (2 * A)) / 3 ^ A) = τ := ⟨_, rfl⟩
  obtain ⟨cQ, hcQ⟩ : ∃ x, Real.posLog (Fintype.card Q) = x := ⟨_, rfl⟩
  obtain ⟨lW, hlW⟩ : ∃ x, Real.log (Rigid.Wd L.B) = x := ⟨_, rfl⟩
  obtain ⟨cUV, hcUV⟩ : ∃ x, Real.posLog ((∑ i, (L.u i : ℝ)) * (∑ j, (L.v j : ℝ))) = x := ⟨_, rfl⟩
  have hlW0 : 0 ≤ lW := hlW ▸ Real.log_nonneg (Rigid.one_le_Wd _)
  have hfl : ∀ x : List (Fin 2), flog L.B x ≤ cQ + x.length * lW := fun x => by
    have := flog_le_length L.B x; rwa [hcQ, hlW] at this
  have hflat : ∀ (g : ℕ → List (Fin 2)) (q : ℕ),
      flog L.B ((List.range q).map g).flatten ≤ cQ + ∑ i ∈ Finset.range q, flog L.B (g i) := fun g q => by
    have := flog_flatten_range L.B g q; rwa [hcQ] at this
  have hav : ∀ ω, Real.posLog (aval L ω : ℝ) ≤ cUV + flog L.B ω := fun ω => by
    have := posLog_aval_le L ω; rwa [hcUV] at this
  have hlogd : 0 ≤ Real.log (Rigid.DxN L.B w ζ ζ : ℝ) := Real.log_natCast_nonneg _
  have hκR : (0 : ℝ) < κ := by exact_mod_cast hκ
  have hdR : (1 : ℝ) ≤ (Rigid.DxN L.B w ζ ζ : ℝ) := by exact_mod_cast hd
  -- Key: for all `m`, `m log d ≤ C + (Lm/κ + P) E Wf`
  have key : ∀ m : ℕ, (m : ℝ) * Real.log (Rigid.DxN L.B w ζ ζ : ℝ) ≤
      (cUV + flog L.B τ + 3 * cQ + ((κ : ℝ) + s.length + 4 * A) * lW) +
        ((w.length : ℝ) * m / κ + P) * (E * Wf) := by
    intro m
    have hy1 : 1 ≤ valW 1 (p ++ wpow w (2 * A) ++ wpow w m ++ s) :=
      le_trans Nat.one_le_two_pow (two_pow_le_valW_one _)
    -- The lower bound for the value (placement, powers)
    have hlow : Rigid.DxN L.B w ζ ζ ^ (2 * A + m) ≤
        aval L (binWord (valW 1 (p ++ wpow w (2 * A) ++ wpow w m ++ s))) := by
      rw [binWord_valW]
      have h1 := aval_ge_path L p (wpow w (2 * A) ++ wpow w m) s ζ
      have h2 : Rigid.DxN L.B w ζ ζ ^ (2 * A + m) ≤ Rigid.DxN L.B (wpow w (2 * A) ++ wpow w m) ζ ζ := by
        rw [← wpow_add]; exact pow_diag_le_wpow L.B w ζ _
      have e : p ++ (wpow w (2 * A) ++ wpow w m) ++ s = p ++ wpow w (2 * A) ++ wpow w m ++ s := by
        simp only [List.append_assoc]
      rw [e] at h1
      calc Rigid.DxN L.B w ζ ζ ^ (2 * A + m) = 1 * Rigid.DxN L.B w ζ ζ ^ (2 * A + m) * 1 := by ring
        _ ≤ (L.u ᵥ* Rigid.DxN L.B p) ζ * Rigid.DxN L.B (wpow w (2 * A) ++ wpow w m) ζ ζ *
              (Rigid.DxN L.B s *ᵥ L.v) ζ := Nat.mul_le_mul (Nat.mul_le_mul hp h2) hs
        _ ≤ _ := h1
    have hpos : 1 ≤ aval L (binWord (valW 1 (p ++ wpow w (2 * A) ++ wpow w m ++ s))) :=
      le_trans (Nat.one_le_pow _ _ hd) hlow
    -- `h3`: the value is positive, so the number is not divisible by 3
    have hy3 : ¬ 3 ∣ valW 1 (p ++ wpow w (2 * A) ++ wpow w m ++ s) := fun h => by
      have := h3 _ hy1 h; omega
    -- The backward chain (Lemma 11.5) and `hT` applied repeatedly
    obtain ⟨n, M, V', hM, _hV', hbn, hn3, hTM, hmid⟩ := hch m hy3
    have hmono := aval_iterate_le L hT M n hn3 hmid
    rw [hTM] at hmono
    -- `log⁺` of the lower bound
    have hstep1 : ((2 * A + m : ℕ) : ℝ) * Real.log (Rigid.DxN L.B w ζ ζ : ℝ) ≤
        Real.posLog (aval L (binWord n) : ℝ) := by
      have e1 : Real.posLog ((Rigid.DxN L.B w ζ ζ : ℝ) ^ (2 * A + m)) =
          ((2 * A + m : ℕ) : ℝ) * Real.log (Rigid.DxN L.B w ζ ζ : ℝ) := by
        rw [Real.posLog_pow, Real.log_of_nat_eq_posLog]
      rw [← e1]
      refine Real.posLog_le_posLog ?_ ?_
      · have := pow_nonneg (zero_le_one.trans hdR) (2 * A + m); linarith
      · exact_mod_cast hlow.trans hmono
    push_cast at hstep1
    -- Upper bound: `bin'(n) = τ ++ (aligned segments ++ rest) ++ β`
    obtain ⟨q, r, hr, hqr⟩ : ∃ q r, r < κ ∧ w.length * m = κ * q + r :=
      ⟨_, _, Nat.mod_lt _ hκ, (Nat.div_add_mod _ _).symm⟩
    have hR := hav (binWord n)
    rw [hbn, hτ, hqr, dig_zero_blocks N D κ q r hD] at hR hstep1
    have b1 := flog_append L.B (τ ++ (((List.range q).map fun i => dig N D (κ * i) κ).flatten ++
      dig N D (κ * q) r)) (bitsF (s.length + M) V')
    have b2 := flog_append L.B τ (((List.range q).map fun i => dig N D (κ * i) κ).flatten ++
      dig N D (κ * q) r)
    have b3 := flog_append L.B (((List.range q).map fun i => dig N D (κ * i) κ).flatten) (dig N D (κ * q) r)
    have b4 := hflat (fun i => dig N D (κ * i) κ) q
    have b5 := hfl (dig N D (κ * q) r)
    have b6 := hfl (bitsF (s.length + M) V')
    simp only [dig_length, bitsF_length] at b5 b6
    push_cast at b6
    have b7 := hwin q
    -- Bounds by the length
    have hrl : (r : ℝ) * lW ≤ κ * lW :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hr.le) hlW0
    have hMl : (M : ℝ) * lW ≤ (4 * A : ℝ) * lW :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hM) hlW0
    have hq : (q : ℝ) ≤ (w.length : ℝ) * m / κ := by
      rw [le_div_iff₀ hκR]
      have h' : ((w.length * m : ℕ) : ℝ) = ((κ * q + r : ℕ) : ℝ) := by rw [hqr]
      push_cast at h'
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      nlinarith
    have hq' : ((q : ℝ) + P) * E * Wf ≤ ((w.length : ℝ) * m / κ + P) * (E * Wf) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hE0 hWf0)
    have hml : (m : ℝ) * Real.log (Rigid.DxN L.B w ζ ζ : ℝ) ≤
        (2 * (A : ℝ) + m) * Real.log (Rigid.DxN L.B w ζ ζ : ℝ) := by
      have : 0 ≤ 2 * (A : ℝ) * Real.log (Rigid.DxN L.B w ζ ζ : ℝ) := mul_nonneg (by positivity) hlogd
      nlinarith
    linarith
  -- `m → ∞`
  have hlin : ∀ m : ℕ, (m : ℝ) * (Real.log (Rigid.DxN L.B w ζ ζ : ℝ) - (w.length : ℝ) / κ * (E * Wf)) ≤
      (cUV + flog L.B τ + 3 * cQ + ((κ : ℝ) + s.length + 4 * A) * lW) + P * (E * Wf) := by
    intro m
    have h := key m
    have e : ((w.length : ℝ) * m / κ + P) * (E * Wf) =
        (m : ℝ) * ((w.length : ℝ) / κ * (E * Wf)) + P * (E * Wf) := by ring
    rw [e] at h
    have e2 : (m : ℝ) * (Real.log (Rigid.DxN L.B w ζ ζ : ℝ) - (w.length : ℝ) / κ * (E * Wf)) =
        (m : ℝ) * Real.log (Rigid.DxN L.B w ζ ζ : ℝ) - (m : ℝ) * ((w.length : ℝ) / κ * (E * Wf)) := by ring
    rw [e2]; linarith
  have h0 := le_of_forall_nat_mul_le hlin
  calc (κ : ℝ) * Real.log (Rigid.DxN L.B w ζ ζ : ℝ) ≤ (κ : ℝ) * ((w.length : ℝ) / κ * (E * Wf)) :=
        mul_le_mul_of_nonneg_left (by linarith) hκR.le
    _ = w.length * (E * Wf) := by field_simp

/-! ## §5 `A → ∞` -/

/-- `3^{c-α} ≤ 3^{c+b_0}/3^A` (`A - b_0 ≤ α`, `b_0 < A`). -/
theorem three_zpow_le {c α A b0 : ℕ} (hb : b0 < A) (hα : A - b0 ≤ α) :
    (3 : ℝ) ^ ((c : ℤ) - α) ≤ (3 : ℝ) ^ (c + b0) / 3 ^ A := by
  rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast, div_le_div_iff₀ (by positivity) (by positivity),
    ← pow_add, ← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- **The diagonal comparison** (Theorem 11.8 for each diagonal word): under `hT` and `h3`, if `ζ` is a relevant index, `w` a non-empty word and
`d := (B_w)_{ζζ} ≥ 1`, then `κ log d ≤ |w| bAvg_κ` for all `κ ≥ 1`. Take `A → ∞` in the bound of `chain_bound`
(`3^{c-α} ≤ 3^{c+b_0}/3^A`; `c` and `b_0` do not depend on `A`). -/
theorem diag_log_le (L : ValAuto Q)
    (hT : ∀ n, 2 ≤ n → ¬ 3 ∣ n → aval L (binWord (Collatz.Arctic.T n)) ≤ aval L (binWord n))
    (h3 : ∀ n, 1 ≤ n → 3 ∣ n → aval L (binWord n) = 0)
    {w : List (Fin 2)} (hw : 1 ≤ w.length) {ζ : Q} (hζ : Rel L ζ)
    (hd : 1 ≤ Rigid.DxN L.B w ζ ζ) {κ : ℕ} (hκ : 1 ≤ κ) :
    (κ : ℝ) * Real.log (Rigid.DxN L.B w ζ ζ : ℝ) ≤ w.length * Rigid.bAvg L.B κ := by
  obtain ⟨p, s, hp, hs⟩ := rel_exists_words L hζ
  obtain ⟨b0, hb0⟩ : ∃ b, padicValNat 3 ((2 ^ w.length - 1) * valW 1 p + valW 0 w) = b := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, 1 + padicValNat 3 (κ * w.length) = c := ⟨_, rfl⟩
  have hWf : Rigid.wsum κ (flog L.B) = 2 ^ κ * Rigid.bAvg L.B κ := wsum_flog L.B κ
  have hb : 0 ≤ Rigid.bAvg L.B κ := bAvg_nonneg L.B κ
  have h2κ : (0 : ℝ) < 2 ^ κ := by positivity
  -- For all `A > b_0` (`m → ∞` has been taken inside `chain_bound`)
  have hA : ∀ A : ℕ, b0 < A → (κ : ℝ) * Real.log (Rigid.DxN L.B w ζ ζ : ℝ) ≤
      w.length * Rigid.bAvg L.B κ + w.length * 2 ^ κ * Rigid.bAvg L.B κ * 3 ^ (c + b0) / 3 ^ A := by
    intro A hA
    obtain ⟨α, hα, hbound⟩ := chain_bound L hT h3 hw hp hs hd hκ (A := A) (by rw [hb0]; exact hA)
    rw [hb0] at hα
    rw [hc, hWf] at hbound
    have h3le := three_zpow_le (c := c) hA hα
    have hL0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
    calc (κ : ℝ) * Real.log (Rigid.DxN L.B w ζ ζ : ℝ)
        ≤ w.length * ((((2 : ℝ) ^ κ)⁻¹ + (3 : ℝ) ^ ((c : ℤ) - α)) * (2 ^ κ * Rigid.bAvg L.B κ)) := hbound
      _ ≤ w.length * ((((2 : ℝ) ^ κ)⁻¹ + (3 : ℝ) ^ (c + b0) / 3 ^ A) * (2 ^ κ * Rigid.bAvg L.B κ)) := by
          gcongr
      _ = _ := by field_simp
  -- `A → ∞`
  by_contra hcon
  push Not at hcon
  obtain ⟨δ, hδ⟩ : ∃ δ, (κ : ℝ) * Real.log (Rigid.DxN L.B w ζ ζ : ℝ) - w.length * Rigid.bAvg L.B κ = δ :=
    ⟨_, rfl⟩
  have hδ0 : 0 < δ := by linarith
  obtain ⟨K, hK⟩ : ∃ K, (w.length : ℝ) * 2 ^ κ * Rigid.bAvg L.B κ * 3 ^ (c + b0) = K := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [← hK]; positivity
  obtain ⟨A0, hA0⟩ := pow_unbounded_of_one_lt (K / δ) (by norm_num : (1 : ℝ) < 3)
  have h1 := hA (max A0 (b0 + 1)) (by omega)
  rw [hK] at h1
  have h3A : (3 : ℝ) ^ A0 ≤ 3 ^ (max A0 (b0 + 1)) := pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
  have hsmall : K / 3 ^ (max A0 (b0 + 1)) < δ := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ0] at hA0
    nlinarith
  linarith

end Collatz.Arctic.NatQ5.W2c

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic W2a W2c

set_option linter.unusedSectionVars false

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-! ## §6 The main theorem -/

/-- **Theorem 11.8 (the diagonal form of the Lyapunov comparison)**: if every index of the value automaton `L` is relevant (`hall`), and the value `V(n) :=`
`aval L (bin'(n))` does not increase along steps of `T` from numbers `n ≥ 2` not divisible by 3 (`hT`) and vanishes on multiples of 3 (`h3`), then for all `κ ≥ 1`
`κ log G ≤ bAvg_κ` (`G := gDiag L.B`, the diagonal `g`; `bAvg_κ` is the uniform average of `log⁺ ‖B_x‖`).
This is exactly the form of the hypothesis `hLC` of `top_rigid` (Lemma 11.3). If `G ≤ 1` it is trivial (`bAvg ≥ 0`). -/
theorem lyap_compare (L : ValAuto Q) (hall : ∀ q, Rel L q)
    (hT : ∀ n, 2 ≤ n → ¬ 3 ∣ n → aval L (binWord (Collatz.Arctic.T n)) ≤ aval L (binWord n))
    (h3 : ∀ n, 1 ≤ n → 3 ∣ n → aval L (binWord n) = 0) :
    ∀ κ : ℕ, 1 ≤ κ → (κ : ℝ) * Real.log (Rigid.gDiag L.B) ≤ Rigid.bAvg L.B κ := by
  intro κ hκ
  have hb := W2c.bAvg_nonneg L.B κ
  have hκR : (0 : ℝ) < κ := by exact_mod_cast hκ
  rcases le_or_gt (Rigid.gDiag L.B) 1 with hG | hG
  · have : Real.log (Rigid.gDiag L.B) ≤ 0 := Real.log_nonpos (Rigid.gDiag_nonneg _) hG
    nlinarith
  · have hG0 : 0 < Rigid.gDiag L.B := by linarith
    have hle : Rigid.gDiag L.B ≤ Real.exp (Rigid.bAvg L.B κ / κ) := by
      unfold Rigid.gDiag
      refine Real.iSup_le (fun pr => ?_) (Real.exp_pos _).le
      obtain ⟨⟨w, hw⟩, i⟩ := pr
      have hwl : 1 ≤ w.length := by
        have : w.length ≠ 0 := by simpa [List.length_eq_zero_iff] using hw
        omega
      have hwlR : (0 : ℝ) < w.length := by exact_mod_cast hwl
      show (Rigid.Dx L.B w i i) ^ ((w.length : ℝ)⁻¹) ≤ _
      rw [Rigid.Dx_apply]
      rcases Nat.eq_zero_or_pos (Rigid.DxN L.B w i i) with h0 | hpos
      · rw [h0, Nat.cast_zero, Real.zero_rpow (inv_ne_zero hwlR.ne')]
        exact (Real.exp_pos _).le
      · have hdR : (0 : ℝ) < (Rigid.DxN L.B w i i : ℝ) := by exact_mod_cast hpos
        rw [Real.rpow_def_of_pos hdR, Real.exp_le_exp]
        have hcore := W2c.diag_log_le L hT h3 hwl (hall i) hpos hκ
        rw [← div_eq_mul_inv, div_le_div_iff₀ hwlR hκR]
        linarith
    have := (Real.log_le_iff_le_exp hG0).2 hle
    rw [le_div_iff₀ hκR] at this
    linarith

/-- The form of the hypothesis of `top_rigid_of_liminf` (the weak form). Follows at once from `lyap_compare`. -/
theorem lyap_compare_liminf (L : ValAuto Q) (hall : ∀ q, Rel L q)
    (hT : ∀ n, 2 ≤ n → ¬ 3 ∣ n → aval L (binWord (Collatz.Arctic.T n)) ≤ aval L (binWord n))
    (h3 : ∀ n, 1 ≤ n → 3 ∣ n → aval L (binWord n) = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ κ : ℕ, N ≤ κ →
      (κ : ℝ) * Real.log (Rigid.gDiag L.B) ≤ Rigid.bAvg L.B κ + ε * κ := by
  intro ε hε
  refine ⟨1, fun κ hκ => ?_⟩
  have := lyap_compare L hall hT h3 κ hκ
  have : 0 ≤ ε * κ := mul_nonneg hε.le (Nat.cast_nonneg κ)
  linarith

end Collatz.Arctic.NatQ5
