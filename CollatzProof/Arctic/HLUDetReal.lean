/-
The deterministic part of the hypothesis `HLeftUse` (`CoreHyp.lean`), part 2: the mantissa criterion at the boundary points and
the lower bound `left_use_ge` on the number of uses of the left-end rules. The combinatorial part is in `HLUDet.lean`.

Correspondence with the paper: the left-end rules in Proposition 6.7 (proof of Proposition B.9 (ii)). Away from the ends, `d = 0, 1, 2` when the mantissa of `n`
lies in `[1, 4/3)`, `[4/3, 5/3)`, `[5/3, 2)`. The log of the mantissa of the block boundary point `P_i` is close to `{a_i log₂ 3 + log₂ t}`.

* `hlu_crit`: for odd `x`, if `(3+d) 2^L ≤ 3x + 1 < (4+d) 2^L` (`L ≥ 1`), then `L = ⌊log₂ x⌋` and
  `T x / 2^{L-1} = 3 + d` (equivalently, the mantissa `x/2^L` lies in `[(3+d)/3 - 2^{-L}/3, (4+d)/3 - 2^{-L}/3)`).
* `hlu_real`: let `3^A 2^k t ≤ x < 3^A 2^k (t+1)`, `y := A log₂ 3 + log₂ t` and `L := ⌊y⌋ + k`. If `{y}` lies in
  `[log₂((3+d)/3), log₂((4+d)/3) - η)` and `t ≥ 2/(1 - 2^{-η})`, the inequalities above hold. Write `x = 2^L 2^{{y}} q`,
  `1 ≤ q < 1 + 1/t`; the deviation of `q` and the term `2^{-L}` are absorbed by the margin `η` (the last term is at most about `2/(t ln 2)`).
* The arc `J_d = [arcLo d η, arcHi d η)`: `arcLo d η = log₂((3+d)/3) + η`, `arcHi d η = log₂((4+d)/3) - η`.
  `J_0 = [η, log₂(4/3) - η)`, `J_1 = [log₂(4/3) + η, log₂(5/3) - η)`, `J_2 = [log₂(5/3) + η, 1 - η)`
  (`hlu_arcLo_zero` etc.). `0 ≤ arcLo`, `arcHi ≤ 1`, and the arcs are nonempty for `η ≤ 1/10` (`hlu_arc_nonempty`).
* `hlu_boundary_crit`: for `m ≥ m₀(η)` and `t ≥ 2^m`, at every boundary `i` with `{a_i log₂ 3 + log₂ t} ∈ J_d`,
  `T P_i / 2^{⌊log₂ P_i⌋ - 1} = 3 + d`.
* **`left_use_ge`**: as a corollary, the number of boundaries in the arc `J_d` is at most the number of uses of `leftRule d` in `m` steps from `x₀`
  (`left_use_ge_sum` is the form with `a_i` written as the sum `Σ (5 or 7)` of the odd steps of the blocks, `oddPrefix` in `HLUWalk.lean`).
-/
import CollatzProof.Arctic.HLUDet

namespace Collatz.Arctic

/-! ## The criterion over the naturals -/

/-- The criterion over the naturals: if `(3+d) 2^L ≤ 3x + 1 < (4+d) 2^L` (`x` odd, `L ≥ 1`), then `T x / 2^{⌊log₂ x⌋ - 1} = 3 + d`. -/
lemma hlu_crit (x d L : ℕ) (hx : x % 2 = 1) (hd : d ≤ 2) (hL : 1 ≤ L)
    (h1 : (3 + d) * 2 ^ L ≤ 3 * x + 1) (h2 : 3 * x + 1 < (4 + d) * 2 ^ L) :
    T x / 2 ^ (Nat.log 2 x - 1) = 3 + d := by
  have hP : 2 ^ L = 2 * 2 ^ (L - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hlog : Nat.log 2 x = L := by
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · interval_cases d <;> omega
    · rw [pow_succ]; interval_cases d <;> omega
  rw [hlog, T_of_odd x hx, Nat.div_div_eq_div_mul, ← hP]
  exact Nat.div_eq_of_lt_le h1 (by rw [show 3 + d + 1 = 4 + d by omega]; exact h2)

/-! ## The real estimate -/

/-- An algebraic auxiliary (upper end): from `X τ < K N₂ F (τ + 1)`, `3F < (4+d) r`, `τ(1 - r) ≥ 2` and `τ < 2 N₂`,
`3X + 1 < (4 + d) N₂ K`. -/
lemma hlu_alg_upper (X τ K N2 F r d : ℝ) (hτ : 1 ≤ τ) (hK : 1 ≤ K) (hN2 : 0 < N2)
    (hr0 : 0 < r) (hr1 : r < 1) (hd : 0 ≤ d)
    (hx : X * τ < K * N2 * F * (τ + 1)) (hF : 3 * F < (4 + d) * r)
    (hε : 2 ≤ τ * (1 - r)) (htN : τ < 2 * N2) :
    3 * X + 1 < (4 + d) * (N2 * K) := by
  set P : ℝ := (4 + d) * K * N2 with hP
  have hKN : 0 < K * N2 * (τ + 1) := by positivity
  have s1 : 3 * X * τ < K * N2 * (τ + 1) * (3 * F) := by
    have : 3 * (X * τ) < 3 * (K * N2 * F * (τ + 1)) := by linarith
    calc 3 * X * τ = 3 * (X * τ) := by ring
      _ < 3 * (K * N2 * F * (τ + 1)) := this
      _ = K * N2 * (τ + 1) * (3 * F) := by ring
  have s2 : K * N2 * (τ + 1) * (3 * F) < K * N2 * (τ + 1) * ((4 + d) * r) :=
    mul_lt_mul_of_pos_left hF hKN
  have s3 : K * N2 * (τ + 1) * ((4 + d) * r) = P * τ - P * (τ - r * τ - r) := by rw [hP]; ring
  have hq : 1 ≤ τ - r * τ - r := by
    have : τ * (1 - r) = τ - r * τ := by ring
    linarith
  have hP4 : 4 * N2 ≤ P := by
    have h1 : 4 * 1 ≤ (4 + d) * K := mul_le_mul (by linarith) hK (by norm_num) (by linarith)
    have h2 : 4 * N2 ≤ (4 + d) * K * N2 := by nlinarith
    rw [hP]; exact h2
  have hP0 : 0 ≤ P := by linarith
  have s4 : P * 1 ≤ P * (τ - r * τ - r) := mul_le_mul_of_nonneg_left hq hP0
  have s5 : 3 * X * τ < (P - 1) * τ := by nlinarith
  have hτ0 : 0 < τ := by linarith
  have s6 : 3 * X < P - 1 := lt_of_mul_lt_mul_right s5 hτ0.le
  have : P = (4 + d) * (N2 * K) := by rw [hP]; ring
  linarith

/-- The real estimate: let `x ∈ [3^A 2^k t, 3^A 2^k (t + 1))`, `y := A log₂ 3 + log₂ t`, `L := ⌊y⌋ + k`.
If `{y}` lies in `[log₂((3+d)/3), log₂((4+d)/3) - η)` and `t ≥ 2/(1 - 2^{-η})`, then `(3+d) 2^L ≤ 3x + 1 < (4+d) 2^L`. -/
lemma hlu_real (η : ℝ) (hη : 0 < η) (x A k t d : ℕ) (hd : d ≤ 2) (ht1 : 1 ≤ t)
    (hx1 : 3 ^ A * 2 ^ k * t ≤ x) (hx2 : x < 3 ^ A * 2 ^ k * (t + 1))
    (hεt : 2 / (1 - (2 : ℝ) ^ (-η)) ≤ t)
    (hlo : Real.logb 2 ((3 + d) / 3) ≤ Int.fract ((A : ℝ) * Real.logb 2 3 + Real.logb 2 t))
    (hhi : Int.fract ((A : ℝ) * Real.logb 2 3 + Real.logb 2 t) < Real.logb 2 ((4 + d) / 3) - η) :
    (3 + d) * 2 ^ (⌊(A : ℝ) * Real.logb 2 3 + Real.logb 2 t⌋₊ + k) ≤ 3 * x + 1 ∧
      3 * x + 1 < (4 + d) * 2 ^ (⌊(A : ℝ) * Real.logb 2 3 + Real.logb 2 t⌋₊ + k) := by
  set Y : ℝ := (A : ℝ) * Real.logb 2 3 + Real.logb 2 t with hYdef
  set N : ℕ := ⌊Y⌋₊ with hN
  set f : ℝ := Int.fract Y with hf
  set r : ℝ := (2 : ℝ) ^ (-η) with hr
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have hY0 : 0 ≤ Y := by
    have h1 : 0 ≤ Real.logb 2 (3 : ℝ) := Real.logb_nonneg (by norm_num) (by norm_num)
    have h2 : 0 ≤ Real.logb 2 (t : ℝ) := Real.logb_nonneg (by norm_num) htR
    positivity
  have hYf : Y = (N : ℝ) + f := by
    rw [hf, ← Int.self_sub_floor, hN, natCast_floor_eq_intCast_floor hY0]; ring
  -- `2^Y = 3^A t = 2^N 2^f`
  have h2Y : (2 : ℝ) ^ Y = 3 ^ A * t := by
    rw [hYdef, Real.rpow_add (by norm_num), mul_comm (A : ℝ), Real.rpow_mul_natCast (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
  have hNF : (3 : ℝ) ^ A * t = 2 ^ N * 2 ^ f := by
    rw [← h2Y, hYf, add_comm, Real.rpow_add_natCast (by norm_num), mul_comm]
  -- `t < 2 · 2^N`
  have htN : (t : ℝ) < 2 * 2 ^ N := by
    have h1 : Y < (N : ℝ) + 1 := Nat.lt_floor_add_one Y
    have h2 : (2 : ℝ) ^ Y < 2 ^ ((N : ℝ) + 1) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h1
    have h3 : (2 : ℝ) ^ ((N : ℝ) + 1) = 2 * 2 ^ N := by
      rw [show (N : ℝ) + 1 = ((N + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, pow_succ, mul_comm]
    have h4 : (t : ℝ) ≤ 3 ^ A * t := le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
    rw [h3, h2Y] at h2
    linarith
  -- bounds on the mantissa `2^f`
  have hFlo : ((3 : ℝ) + d) / 3 ≤ 2 ^ f := by
    have := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num) hlo
    rwa [Real.rpow_logb (by norm_num) (by norm_num) (by positivity)] at this
  have hFhi : (2 : ℝ) ^ f < ((4 : ℝ) + d) / 3 * r := by
    have := Real.rpow_lt_rpow_of_exponent_lt (x := (2 : ℝ)) (by norm_num) hhi
    rwa [sub_eq_add_neg, Real.rpow_add (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) (by positivity)] at this
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hεt' : 2 ≤ (t : ℝ) * (1 - r) := by
    rwa [div_le_iff₀ (by linarith)] at hεt
  have hx1R : (3 : ℝ) ^ A * 2 ^ k * t ≤ x := by exact_mod_cast hx1
  have hx2R : (x : ℝ) < 3 ^ A * 2 ^ k * (t + 1) := by exact_mod_cast hx2
  have hK1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hN2 : (0 : ℝ) < 2 ^ N := by positivity
  have hF0 : (0 : ℝ) < 2 ^ f := Real.rpow_pos_of_pos (by norm_num) _
  have hdR : (d : ℝ) ≤ 2 := by exact_mod_cast hd
  have hd0 : (0 : ℝ) ≤ d := by positivity
  set a : ℝ := (3 : ℝ) ^ A with ha
  set K : ℝ := (2 : ℝ) ^ k with hK
  set N2 : ℝ := (2 : ℝ) ^ N with hN2def
  set F : ℝ := (2 : ℝ) ^ f with hF
  set τ : ℝ := (t : ℝ) with hτ
  set X : ℝ := (x : ℝ) with hX
  have hpow : ((2 ^ (N + k) : ℕ) : ℝ) = N2 * K := by push_cast; rw [pow_add]
  constructor
  · -- lower end
    have key : ((3 : ℝ) + d) * (N2 * K) ≤ 3 * X := by
      have h1 : ((3 : ℝ) + d) * (N2 * K) ≤ 3 * F * (N2 * K) := by
        have := mul_le_mul_of_nonneg_right hFlo (le_of_lt (mul_pos hN2 (by linarith : (0:ℝ) < K)))
        linarith
      have h2 : 3 * F * (N2 * K) = 3 * (a * τ) * K := by rw [hNF]; ring
      nlinarith
    have : (((3 + d) * 2 ^ (N + k) : ℕ) : ℝ) ≤ ((3 * x + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_mul, hpow]; push_cast; linarith
    exact_mod_cast this
  · -- upper end
    have h1 : X * τ < K * N2 * F * (τ + 1) := by
      have hτ0 : 0 < τ := by linarith
      have e : K * N2 * F * (τ + 1) = a * K * (τ + 1) * τ := by
        calc K * N2 * F * (τ + 1) = K * (N2 * F) * (τ + 1) := by ring
          _ = a * K * (τ + 1) * τ := by rw [← hNF]; ring
      rw [e]
      exact mul_lt_mul_of_pos_right hx2R hτ0
    have h11 := hlu_alg_upper X τ K N2 F r d htR hK1 hN2 hr0 hr1 hd0 h1
      (by linarith) hεt' htN
    have : ((3 * x + 1 : ℕ) : ℝ) < (((4 + d) * 2 ^ (N + k) : ℕ) : ℝ) := by
      rw [Nat.cast_mul, hpow]; push_cast; linarith
    exact_mod_cast this

/-! ## Arcs -/

noncomputable def arcLo (d : ℕ) (η : ℝ) : ℝ := Real.logb 2 ((3 + d) / 3) + η
noncomputable def arcHi (d : ℕ) (η : ℝ) : ℝ := Real.logb 2 ((4 + d) / 3) - η

theorem hlu_arcLo_zero (η : ℝ) : arcLo 0 η = η := by simp [arcLo]
theorem hlu_arcHi_two (η : ℝ) : arcHi 2 η = 1 - η := by
  unfold arcHi; norm_num
theorem hlu_arcHi_zero (η : ℝ) : arcHi 0 η = Real.logb 2 (4 / 3) - η := by simp [arcHi]
theorem hlu_arcLo_one (η : ℝ) : arcLo 1 η = Real.logb 2 (4 / 3) + η := by unfold arcLo; norm_num
theorem hlu_arcHi_one (η : ℝ) : arcHi 1 η = Real.logb 2 (5 / 3) - η := by unfold arcHi; norm_num
theorem hlu_arcLo_two (η : ℝ) : arcLo 2 η = Real.logb 2 (5 / 3) + η := by unfold arcLo; norm_num

theorem hlu_arcLo_nonneg (d : ℕ) (η : ℝ) (hη : 0 ≤ η) : 0 ≤ arcLo d η := by
  unfold arcLo
  have : 0 ≤ Real.logb 2 ((3 + d) / 3) := Real.logb_nonneg (by norm_num) (by
    rw [le_div_iff₀ (by norm_num)]; have : (0:ℝ) ≤ d := by positivity
    linarith)
  linarith

theorem hlu_arcHi_le_one (d : ℕ) (hd : d ≤ 2) (η : ℝ) (hη : 0 ≤ η) : arcHi d η ≤ 1 := by
  unfold arcHi
  have hdR : (d : ℝ) ≤ 2 := by exact_mod_cast hd
  have : Real.logb 2 ((4 + d) / 3) ≤ 1 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_one]
    linarith
  linarith

/-- The arcs are nonempty for `η ≤ 1/10` (`log₂ ((4+d)/(3+d)) ≥ log₂ (6/5) > 1/5`). -/
theorem hlu_arc_nonempty (d : ℕ) (hd : d ≤ 2) (η : ℝ) (hη : η ≤ 1 / 10) : arcLo d η < arcHi d η := by
  unfold arcLo arcHi
  have hdR : (d : ℝ) ≤ 2 := by exact_mod_cast hd
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have h1 : Real.logb 2 ((4 + d) / 3) - Real.logb 2 ((3 + d) / 3) = Real.logb 2 ((4 + d) / (3 + d)) := by
    rw [← Real.logb_div (by positivity) (by positivity)]
    congr 1
    field_simp
  have h2 : (1 : ℝ) / 5 < Real.logb 2 ((4 + d) / (3 + d)) := by
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity)]
    have h3 : (2 : ℝ) ^ ((1 : ℝ) / 5) < 6 / 5 := by
      rw [show (6 : ℝ) / 5 = ((6 / 5) ^ (5 : ℝ)) ^ ((1 : ℝ) / 5) by
        rw [← Real.rpow_mul (by norm_num)]; norm_num]
      exact Real.rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
    have h4 : (6 : ℝ) / 5 ≤ (4 + d) / (3 + d) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
    linarith
  linarith

/-! ## The criterion at the boundary points and the main theorem -/

/-- **Criterion at the boundary points**: for `m ≥ m₀(η)` and `t ≥ 2^m`, at every boundary `i` with `{a_i log₂ 3 + log₂ t} ∈ J_d`,
the top window of the boundary point `P_i` is `3 + d`. -/
theorem hlu_boundary_crit (η : ℝ) (hη : 0 < η) : ∃ m₀ : ℕ, ∀ (β : List Bool) (t d i : ℕ),
    m₀ ≤ (parityOf β).length → 2 ^ (parityOf β).length ≤ t → d ≤ 2 → i < β.length →
    arcLo d η ≤ Int.fract ((terrasA (parityOf (β.take i)) : ℝ) * Real.logb 2 3 + Real.logb 2 t) →
    Int.fract ((terrasA (parityOf (β.take i)) : ℝ) * Real.logb 2 3 + Real.logb 2 t) < arcHi d η →
    T (T^[blockEnd β i] (terrasR (parityOf β) + 2 ^ (parityOf β).length * t))
      / 2 ^ (Nat.log 2 (T^[blockEnd β i] (terrasR (parityOf β) + 2 ^ (parityOf β).length * t)) - 1)
      = 3 + d := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 / (1 - (2 : ℝ) ^ (-η))) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n, ?_⟩
  intro β t d i hm ht hd hi hlo hhi
  have ht1 : 1 ≤ t := le_trans Nat.one_le_two_pow ht
  have hεt : 2 / (1 - (2 : ℝ) ^ (-η)) ≤ (t : ℝ) := by
    have h1 : 2 ^ n ≤ t := le_trans (Nat.pow_le_pow_right (by norm_num) hm) ht
    have h2 : (2 : ℝ) ^ n ≤ (t : ℝ) := by exact_mod_cast h1
    linarith
  obtain ⟨hb1, hb2⟩ := hlu_P_bounds β t i
  have hk : 8 ≤ (parityOf β).length - blockEnd β i := by
    have := hlu_blockEnd_add_le β i hi; omega
  unfold arcLo at hlo
  unfold arcHi at hhi
  obtain ⟨h1, h2⟩ := hlu_real η hη _ _ _ t d hd ht1 hb1 hb2 hεt (by linarith) hhi
  exact hlu_crit _ d _ (hlu_P_odd β t i hi) hd (by omega) h1 h2

/-- **Lower bound on the number of uses of the left-end rules** (the deterministic part of `HLeftUse`): for `η > 0` there is `m₀` such that, for `m ≥ m₀`, `t ≥ 2^m`
and `d ≤ 2`, the number of indices `i < |β|` for which the log of the mantissa `{a_i log₂ 3 + log₂ t}` of the block boundary point lies in the arc `J_d` is
at most the number of uses of `leftRule d` in the canonical derivations along the `m` steps from `x₀ = r_σ + 2^m t`. -/
theorem left_use_ge (η : ℝ) (hη : 0 < η) : ∃ m₀ : ℕ, ∀ (β : List Bool) (t d : ℕ),
    m₀ ≤ (parityOf β).length → 2 ^ (parityOf β).length ≤ t → d ≤ 2 →
    (((Finset.range β.length).filter (fun i =>
        arcLo d η ≤ Int.fract ((terrasA (parityOf (β.take i)) : ℝ) * Real.logb 2 3 + Real.logb 2 t) ∧
        Int.fract ((terrasA (parityOf (β.take i)) : ℝ) * Real.logb 2 3 + Real.logb 2 t) < arcHi d η)).card) ≤
      usesOrbit (leftRule d) (terrasR (parityOf β) + 2 ^ (parityOf β).length * t) (parityOf β).length := by
  obtain ⟨m₀, hm₀⟩ := hlu_boundary_crit η hη
  refine ⟨m₀, fun β t d hm ht hd => ?_⟩
  refine le_trans (Finset.card_le_card ?_)
    (hlu_usesOrbit_ge_boundary β t d (le_trans Nat.one_le_two_pow ht) hd)
  apply Finset.monotone_filter_right
  intro i hi hp
  exact hm₀ β t d i hm ht hd (Finset.mem_range.mp hi) hp.1 hp.2

/-- The form of `left_use_ge` with `a_i` written as the sum of the numbers of odd steps of the blocks (5 for `X'`, 7 for `Y'`) (`oddPrefix β i` in
`HLUWalk.lean` is definitionally this sum). -/
theorem left_use_ge_sum (η : ℝ) (hη : 0 < η) : ∃ m₀ : ℕ, ∀ (β : List Bool) (t d : ℕ),
    m₀ ≤ (parityOf β).length → 2 ^ (parityOf β).length ≤ t → d ≤ 2 →
    (((Finset.range β.length).filter (fun i =>
        arcLo d η ≤ Int.fract ((((β.take i).map (fun x => if x then 5 else 7)).sum : ℕ) * Real.logb 2 3
          + Real.logb 2 t) ∧
        Int.fract ((((β.take i).map (fun x => if x then 5 else 7)).sum : ℕ) * Real.logb 2 3
          + Real.logb 2 t) < arcHi d η)).card) ≤
      usesOrbit (leftRule d) (terrasR (parityOf β) + 2 ^ (parityOf β).length * t) (parityOf β).length := by
  obtain ⟨m₀, hm₀⟩ := left_use_ge η hη
  refine ⟨m₀, fun β t d hm ht hd => ?_⟩
  have := hm₀ β t d hm ht hd
  simp only [hlu_terrasA_take] at this
  exact this

end Collatz.Arctic
