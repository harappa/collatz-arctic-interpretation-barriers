/-
# Natural-number interpretations of 𝒯 (Section 12.5): the event (ii), the top window of the end point (Proposition 12.19)

Earlier written arguments (not used here) obtained this event from the equidistribution of `{A_σ log₂3}` by Weyl's criterion
(`A_σ` is the number `a_σ` of odd steps). Since only a positive lower bound for the probability is needed, it is proved here
without Weyl's criterion, from `HLUWalk.walk_dense` (the argument of the proof of Proposition B.9 (i)) and the freedom of the last `B` blocks.
(In Proposition 12.19 the word `τ` of length `E` is `w_top` of length `L_τ`, and the integer `T₀` is `τ`.)

**The family** (`Family.lean`, the model of `T` of Section 6.1): `t := T₀ 2^{n-K} + 2^{s'} u + ρ`, `x₁ := c_σ + 3^{A_σ} t`. The top
window for 𝒯 consists of the `E` digits after the leading 1, i.e. the first `E` letters of `binWord` (`ValueAuto.lean`). `K := E + 9`,
`T₀ := 1 τ 0^8` (`topT0 τ`).

**The route** (checked after internal review): `{log₂ T₀}` is the left end of `I(τ)`, so the condition on `σ` for the top window of the end point to be `τ`
does not depend on `τ`: "`3^{A_σ}` is at most `1 + 2^{-E-2}` times a power of two `2^e`" (`PowNear`); in terms of the logarithm of the mantissa,
`{A_σ log₂3} ∈ [0, log₂(1 + 2^{-E-2}))`. This arc does not wrap around 0 (it has the form `[0, ·)`), so it fits the hypothesis
`0 ≤ lo < hi ≤ 1` of `walk_dense` directly. It is a sub-arc of `J(τ)` of the written argument (`I(τ)` shrunk by `2^{3-K}` on both sides), and does not depend on `τ`.

* `topT0`, `topT0_eq`, `topT0_bounds`, `binWord_topT0`: `T₀ = 2^8 (2^E + val τ)`, `2^{K-1} ≤ T₀ < 2^K`.
* `top_of_powNear` (deterministic): if `PowNear E A_σ`, then `(binWord x₁).take E = τ` for all `n`, `u` with `K + s' ≤ n`, `u < 2^{n-K-s'}`, and
  all `τ` of length `E`. `top_X0`: the starting point also has `(binWord x₀).take E = τ` (independently of `σ`).
* `powNear_of_fract` (real analysis): if `{A log₂3} < log₂(1 + 2^{-E-2})`, then `PowNear E A`.
* `powNear_walk` (`walk_dense`, `α = -2 log₂3`): there is `B` such that for every `A₀` there is `j < B` with
  `PowNear E (A₀ + 5j + 7(B - j))`.
* `powNear_prob`: if `k ≥ B`, then `Pr(PowNear E A_σ) ≥ (3/10)^B` (for each choice of the first `k - B` blocks, the last `B` blocks are chosen as the pattern
  `X'^j Y'^{B-j}`; `sum_split`).
* **`top_window`**: `∃ c > 0, ∃ B, ∀ β₀ k, B ≤ k → c ≤ Pr(∀ τ n u, … → (binWord x₁).take E = τ)`.

The family as a whole is not conditioned (the event is combined with the other events on `σ` by the union bound `Prσ_and_ge`). All auxiliary declarations are in the namespace
`Collatz.Arctic.NatQ5.W3b`. No `sorry`, `axiom` or `native_decide` is used.
-/
import CollatzProof.Arctic.Nat.W3bBase

namespace Collatz.Arctic.NatQ5.W3b

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W2a Finset
open Classical

/-! ## §1 The number of the top window `T₀ = 1 τ 0^8` -/

/-- `T₀ := 1 τ 0^8` (`K = |τ| + 9` digits; the `|τ|` digits after the leading 1 are `τ`). -/
def topT0 (τ : List (Fin 2)) : ℕ := valW 1 (τ ++ List.replicate 8 0)

theorem valW_replicate_zero (r j : ℕ) : valW r (List.replicate j (0 : Fin 2)) = r * 2 ^ j := by
  induction j generalizing r with
  | zero => simp [valW]
  | succ j ih =>
    rw [List.replicate_succ, valW_cons, ih, pow_succ]
    simp only [Fin.val_zero, add_zero]
    ring

/-- `T₀ = 2^8 (2^{|τ|} + val τ)`. -/
theorem topT0_eq (τ : List (Fin 2)) : topT0 τ = 2 ^ 8 * (2 ^ τ.length + valW 0 τ) := by
  unfold topT0
  rw [valW_append, valW_replicate_zero, valW_one]
  ring

/-- `2^{K-1} ≤ T₀ < 2^K` (`K = |τ| + 9`). -/
theorem topT0_bounds (τ : List (Fin 2)) :
    2 ^ (τ.length + 8) ≤ topT0 τ ∧ topT0 τ < 2 ^ (τ.length + 9) := by
  rw [topT0_eq]
  have h := valW_lt τ
  constructor
  · rw [pow_add, mul_comm (2 ^ τ.length)]
    exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  · have e : 2 ^ (τ.length + 9) = 2 ^ 8 * (2 * 2 ^ τ.length) := by
      rw [show τ.length + 9 = 8 + (τ.length + 1) by omega, pow_add, pow_succ]; ring
    rw [e]
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)

theorem binWord_topT0 (τ : List (Fin 2)) : binWord (topT0 τ) = τ ++ List.replicate 8 0 :=
  binWord_valW _

theorem binWord_one : binWord 1 = [] := binWord_valW []

/-! ## §2 The deterministic part: if `3^A` is close to a power of two, the top window is `τ` -/

/-- `3^A` is at most `1 + 2^{-E-2}` times a power of two `2^e` (in terms of the logarithm of the mantissa, `{A log₂3} ∈ [0, log₂(1 + 2^{-E-2})]`). -/
def PowNear (E A : ℕ) : Prop :=
  ∃ e : ℕ, 2 ^ e ≤ 3 ^ A ∧ 3 ^ A * 2 ^ (E + 2) ≤ 2 ^ e * (2 ^ (E + 2) + 1)

/-- The key inequality: if `X 2^{E+2} ≤ Y (2^{E+2} + 1)` and `P < 2^{E+1}`, then `X (2^8 P + 1) ≤ Y 2^8 (P + 1)`. -/
theorem top_key {X Y E P : ℕ} (hXY : X * 2 ^ (E + 2) ≤ Y * (2 ^ (E + 2) + 1))
    (hP : P < 2 ^ (E + 1)) : X * (2 ^ 8 * P + 1) ≤ Y * 2 ^ 8 * (P + 1) := by
  set Z := 2 ^ (E + 1) with hZ
  have h2 : 2 ^ (E + 2) = 2 * Z := by rw [hZ, pow_succ]; ring
  rw [h2] at hXY
  have hZpos : 0 < 2 * Z := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hZpos
  have hbound : (2 * Z + 1) * (2 ^ 8 * P + 1) ≤ 2 ^ 8 * (P + 1) * (2 * Z) := by
    have : P + 1 ≤ Z := hP
    nlinarith
  calc X * (2 ^ 8 * P + 1) * (2 * Z) = X * (2 * Z) * (2 ^ 8 * P + 1) := by ring
    _ ≤ Y * (2 * Z + 1) * (2 ^ 8 * P + 1) := Nat.mul_le_mul_right _ hXY
    _ = Y * ((2 * Z + 1) * (2 ^ 8 * P + 1)) := by ring
    _ ≤ Y * (2 ^ 8 * (P + 1) * (2 * Z)) := Nat.mul_le_mul_left _ hbound
    _ = Y * 2 ^ 8 * (P + 1) * (2 * Z) := by ring

/-- Reading off the top window: if `2^N P ≤ x < 2^N (P + 1)`, `P = 2^E + θ` and `θ < 2^E`, then `(binWord x).take E = bitsF E θ`. -/
theorem take_binWord_of_bounds {x N E θ : ℕ} (hθ : θ < 2 ^ E)
    (h1 : 2 ^ N * (2 ^ E + θ) ≤ x) (h2 : x < 2 ^ N * (2 ^ E + θ + 1)) :
    (binWord x).take E = bitsF E θ := by
  set r := x - 2 ^ N * (2 ^ E + θ) with hr
  have hrlt : r < 2 ^ N := by
    have : 2 ^ N * (2 ^ E + θ + 1) = 2 ^ N * (2 ^ E + θ) + 2 ^ N := by ring
    omega
  have hx : x = 1 * 2 ^ (N + E) + θ * 2 ^ N + r := by
    rw [pow_add]
    have : 2 ^ N * (2 ^ E + θ) = 1 * (2 ^ N * 2 ^ E) + θ * 2 ^ N := by ring
    omega
  rw [hx, binWord_split 1 θ r N E le_rfl hθ hrlt, binWord_one, List.nil_append]
  exact List.take_left' (bitsF_length E θ)

/-- **The deterministic part of (ii)**: if `PowNear E A_σ`, the top window of the end point `x₁` is `τ` (`|τ| = E`). -/
theorem top_of_powNear {E : ℕ} {β₀ β : List Bool} {n u : ℕ} (τ : List (Fin 2)) (hτ : τ.length = E)
    (hKn : E + 9 + (parityOf β₀).length ≤ n)
    (hu : u < 2 ^ (n - (E + 9) - (parityOf β₀).length))
    (hg : PowNear E (terrasA (parityOf β))) :
    (binWord (famX1 β₀ β n (E + 9) (topT0 τ) u)).take E = τ := by
  obtain ⟨e, he1, he2⟩ := hg
  set A := terrasA (parityOf β) with hA
  set θ := valW 0 τ with hθdef
  have hθ : θ < 2 ^ E := by rw [hθdef, ← hτ]; exact valW_lt τ
  set P := 2 ^ E + θ with hP
  have hT0 : topT0 τ = 2 ^ 8 * P := by rw [topT0_eq, hτ]
  set D := 2 ^ (n - (E + 9)) with hD
  set low := 2 ^ (parityOf β₀).length * u + famRho β₀ β with hlow
  have hlow_lt : low < D := fam_low_lt (β := β) hKn hu
  have ht : famT β₀ β n (E + 9) (topT0 τ) u = 2 ^ 8 * P * D + low := by
    unfold famT; rw [hT0, hD, hlow]; ring
  have hc := terrasC_lt (parityOf β)
  rw [← hA] at hc
  have hx : famX1 β₀ β n (E + 9) (topT0 τ) u = terrasC (parityOf β) + 3 ^ A * (2 ^ 8 * P * D + low) := by
    unfold famX1; rw [ht]
  set N := e + 8 + (n - (E + 9)) with hN
  have h2N : 2 ^ N = 2 ^ e * 2 ^ 8 * D := by rw [hN, pow_add, pow_add]
  have hPlt : P < 2 ^ (E + 1) := by rw [hP, pow_succ]; omega
  have hkey := top_key he2 hPlt
  have hτb : bitsF E θ = τ := by rw [hθdef, ← hτ, bitsF_valW]
  suffices hs : (binWord (famX1 β₀ β n (E + 9) (topT0 τ) u)).take E = bitsF E θ by rwa [hτb] at hs
  apply take_binWord_of_bounds (N := N) hθ
  · -- lower bound: `2^N P ≤ 3^A 2^8 P D ≤ x₁`
    rw [hx, h2N]
    have : 2 ^ e * 2 ^ 8 * D * P ≤ 3 ^ A * (2 ^ 8 * P * D) := by
      calc 2 ^ e * 2 ^ 8 * D * P = 2 ^ e * (2 ^ 8 * P * D) := by ring
        _ ≤ 3 ^ A * (2 ^ 8 * P * D) := Nat.mul_le_mul_right _ he1
    have h3 : 3 ^ A * (2 ^ 8 * P * D) ≤ 3 ^ A * (2 ^ 8 * P * D + low) :=
      Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    calc 2 ^ e * 2 ^ 8 * D * P ≤ 3 ^ A * (2 ^ 8 * P * D) := this
      _ ≤ _ := h3
      _ ≤ _ := Nat.le_add_left _ _
  · -- upper bound: `x₁ < 3^A (t + 1) ≤ 3^A (2^8 P + 1) D ≤ 2^e 2^8 (P + 1) D = 2^N (P + 1)`
    rw [hx, h2N]
    have h1 : terrasC (parityOf β) + 3 ^ A * (2 ^ 8 * P * D + low) < 3 ^ A * ((2 ^ 8 * P + 1) * D) := by
      have : 3 ^ A * (2 ^ 8 * P * D + low + 1) ≤ 3 ^ A * ((2 ^ 8 * P + 1) * D) :=
        Nat.mul_le_mul_left _ (by nlinarith)
      have e1 : 3 ^ A * (2 ^ 8 * P * D + low + 1) = 3 ^ A * (2 ^ 8 * P * D + low) + 3 ^ A := by ring
      omega
    calc terrasC (parityOf β) + 3 ^ A * (2 ^ 8 * P * D + low) < 3 ^ A * ((2 ^ 8 * P + 1) * D) := h1
      _ = 3 ^ A * (2 ^ 8 * P + 1) * D := by ring
      _ ≤ 2 ^ e * 2 ^ 8 * (P + 1) * D := Nat.mul_le_mul_right _ hkey
      _ = 2 ^ e * 2 ^ 8 * D * (2 ^ E + θ + 1) := by rw [hP]; ring

/-- The top window of the starting point `x₀ = r_σ + 2^m t` is also `τ` (independently of `σ`). -/
theorem top_X0 {E : ℕ} {β₀ β : List Bool} {n u : ℕ} (τ : List (Fin 2)) (hτ : τ.length = E)
    (hKn : E + 9 + (parityOf β₀).length ≤ n)
    (hu : u < 2 ^ (n - (E + 9) - (parityOf β₀).length)) :
    (binWord (famX0 β₀ β n (E + 9) (topT0 τ) u)).take E = τ := by
  set θ := valW 0 τ with hθdef
  have hθ : θ < 2 ^ E := by rw [hθdef, ← hτ]; exact valW_lt τ
  set m := (parityOf β).length with hm
  set D := 2 ^ (n - (E + 9)) with hD
  set low := 2 ^ (parityOf β₀).length * u + famRho β₀ β with hlow
  have hlow_lt : low < D := fam_low_lt (β := β) hKn hu
  have hr := terrasR_lt (parityOf β)
  rw [← hm] at hr
  have hT0 : topT0 τ = 2 ^ 8 * (2 ^ E + θ) := by rw [topT0_eq, hτ]
  have hx : famX0 β₀ β n (E + 9) (topT0 τ) u
      = 2 ^ (8 + m + (n - (E + 9))) * (2 ^ E + θ) + (2 ^ m * low + terrasR (parityOf β)) := by
    unfold famX0 famT
    rw [hT0, ← hm, pow_add, pow_add]
    ring
  have hτb : bitsF E θ = τ := by rw [hθdef, ← hτ, bitsF_valW]
  suffices hs : (binWord (famX0 β₀ β n (E + 9) (topT0 τ) u)).take E = bitsF E θ by rwa [hτb] at hs
  apply take_binWord_of_bounds (N := 8 + m + (n - (E + 9))) hθ
  · rw [hx]; exact Nat.le_add_right _ _
  · rw [hx]
    have hV : 2 ^ m * low + terrasR (parityOf β) < 2 ^ (8 + m + (n - (E + 9))) := by
      have : 2 ^ m * (low + 1) ≤ 2 ^ m * D := Nat.mul_le_mul_left _ hlow_lt
      have e : 2 ^ (8 + m + (n - (E + 9))) = 2 ^ 8 * (2 ^ m * D) := by
        rw [hD, pow_add, pow_add]; ring
      have : 2 ^ m * D ≤ 2 ^ 8 * (2 ^ m * D) := Nat.le_mul_of_pos_left _ (by positivity)
      nlinarith
    nlinarith

/-! ## §3 Real analysis: if the logarithm of the mantissa lies in the arc, then `PowNear` -/

/-- If `{A log₂3} < log₂(1 + 2^{-E-2})`, then `PowNear E A`. -/
theorem powNear_of_fract (E A : ℕ)
    (h : Int.fract ((A : ℝ) * Real.logb 2 3) < Real.logb 2 (1 + 1 / 2 ^ (E + 2))) :
    PowNear E A := by
  set z : ℝ := (A : ℝ) * Real.logb 2 3 with hz
  have hl3 : 0 < Real.logb 2 3 := Real.logb_pos (by norm_num) (by norm_num)
  have hz0 : 0 ≤ z := mul_nonneg (Nat.cast_nonneg _) hl3.le
  set e' : ℤ := ⌊z⌋ with he'
  have he'0 : 0 ≤ e' := Int.floor_nonneg.mpr hz0
  set e : ℕ := e'.toNat with he
  have hee : ((e : ℤ) : ℝ) = (e' : ℝ) := by rw [he, Int.toNat_of_nonneg he'0]
  have hee' : (e : ℝ) = (e' : ℝ) := by rw [← hee]; rfl
  have hfr : Int.fract z = z - e := by rw [hee']; rfl
  -- `2^z = 3^A`
  have h2z : (2 : ℝ) ^ z = 3 ^ A := by
    rw [hz, mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num)
      (by norm_num), Real.rpow_natCast]
  refine ⟨e, ?_, ?_⟩
  · -- `2^e ≤ 2^z = 3^A`
    have hle : (e : ℝ) ≤ z := by rw [hee']; exact Int.floor_le z
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hle
    rw [Real.rpow_natCast, h2z] at this
    exact_mod_cast this
  · -- `3^A = 2^e 2^{fract z} < 2^e (1 + 2^{-E-2})`
    have hδ : (0 : ℝ) < 1 + 1 / 2 ^ (E + 2) := by positivity
    have hsplit : (2 : ℝ) ^ z = 2 ^ e * 2 ^ (Int.fract z) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num), hfr]
      congr 1; ring
    have hlt : (2 : ℝ) ^ (Int.fract z) < 1 + 1 / 2 ^ (E + 2) := by
      have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) h
      rwa [Real.rpow_logb (by norm_num) (by norm_num) hδ] at this
    have h3 : (3 : ℝ) ^ A < 2 ^ e * (1 + 1 / 2 ^ (E + 2)) := by
      rw [← h2z, hsplit]
      exact mul_lt_mul_of_pos_left hlt (by positivity)
    have h4 : ((3 ^ A * 2 ^ (E + 2) : ℕ) : ℝ) < ((2 ^ e * (2 ^ (E + 2) + 1) : ℕ) : ℝ) := by
      push_cast
      have hp : (0 : ℝ) < 2 ^ (E + 2) := by positivity
      calc (3 : ℝ) ^ A * 2 ^ (E + 2) < 2 ^ e * (1 + 1 / 2 ^ (E + 2)) * 2 ^ (E + 2) :=
            mul_lt_mul_of_pos_right h3 hp
        _ = 2 ^ e * (2 ^ (E + 2) + 1) := by field_simp
    exact (Nat.cast_lt.mp h4).le

/-! ## §4 Density: choosing the pattern of the last `B` blocks -/

/-- `log₂(1 + 2^{-E-2})` lies in `(0, 1]`. -/
theorem arc_bounds (E : ℕ) :
    0 < Real.logb 2 (1 + 1 / 2 ^ (E + 2)) ∧ Real.logb 2 (1 + 1 / 2 ^ (E + 2)) ≤ 1 := by
  have hp : (0 : ℝ) < 1 / 2 ^ (E + 2) := by positivity
  have hp1 : (1 : ℝ) / 2 ^ (E + 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  constructor
  · exact Real.logb_pos (by norm_num) (by linarith)
  · calc Real.logb 2 (1 + 1 / 2 ^ (E + 2)) ≤ Real.logb 2 2 :=
          Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
      _ = 1 := Real.logb_self_eq_one (by norm_num)

/-- **Application of the finite form of density** (`walk_dense`, `α = -2 log₂3`): there is `B > 0` such that for every `A₀` there is `j < B` with
`PowNear E (A₀ + 5j + 7(B - j))` (the last `B` blocks are taken to be `X'^j Y'^{B-j}`). -/
theorem powNear_walk (E : ℕ) :
    ∃ B : ℕ, 0 < B ∧ ∀ A₀ : ℕ, ∃ j < B, PowNear E (A₀ + 5 * j + 7 * (B - j)) := by
  have hirr : Irrational (-(2 * Real.logb 2 3)) := by
    have := walk_irrational_logb.natCast_mul (m := 2) (by norm_num)
    simpa using this.neg
  obtain ⟨hlo, hhi⟩ := arc_bounds E
  obtain ⟨B, hB⟩ := walk_dense _ hirr 0 _ le_rfl hlo hhi
  have hBpos : 0 < B := by
    obtain ⟨j, hj, -⟩ := hB 0
    omega
  refine ⟨B, hBpos, fun A₀ => ?_⟩
  obtain ⟨j, hj, -, hj2⟩ := hB (((A₀ + 7 * B : ℕ) : ℝ) * Real.logb 2 3)
  refine ⟨j, hj, powNear_of_fract E _ ?_⟩
  have e : (((A₀ + 5 * j + 7 * (B - j) : ℕ) : ℝ)) * Real.logb 2 3
      = ((A₀ + 7 * B : ℕ) : ℝ) * Real.logb 2 3 + (j : ℝ) * (-(2 * Real.logb 2 3)) := by
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hj.le,
      Nat.cast_add, Nat.cast_mul]
    ring
  rw [e]
  exact hj2

/-- The pattern `X'^j Y'^{B-j}` of the last `B` blocks. -/
def topTail (B j : ℕ) : List Bool := List.replicate j true ++ List.replicate (B - j) false

theorem topTail_mem {B j : ℕ} (hj : j ≤ B) : topTail B j ∈ blockChoices B := by
  rw [fam_mem_blockChoices, topTail, List.length_append, List.length_replicate,
    List.length_replicate]
  omega

theorem topTail_terrasA (B j : ℕ) (l : List Bool) :
    terrasA (parityOf (l ++ topTail B j)) = terrasA (parityOf l) + 5 * j + 7 * (B - j) := by
  rw [fam_parityOf_append, terrasA_append, terrasA_eq (parityOf (topTail B j)),
    (fam_parityOf_counts _).2.1]
  simp [topTail, List.count_replicate]
  ring

theorem topTail_wt {B j : ℕ} (hj : j ≤ B) : (3 / 10 : ℚ) ^ B ≤ wtβ (topTail B j) := by
  rw [topTail, wtβ_append, wtβ_replicate, wtβ_replicate]
  simp only [↓reduceIte, Bool.false_eq_true]
  calc (3 / 10 : ℚ) ^ B = (3 / 10) ^ j * (3 / 10) ^ (B - j) := by
        rw [← pow_add, Nat.add_sub_cancel' hj]
    _ ≤ (3 / 10) ^ j * (7 / 10) ^ (B - j) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num) _) (by positivity)

/-- **The probability of (ii)**: if `k ≥ B`, then `Pr(PowNear E A_σ) ≥ (3/10)^B` (`B` depends only on `E`). -/
theorem powNear_prob (E : ℕ) :
    ∃ B : ℕ, 0 < B ∧ ∀ (β₀ : List Bool) (k : ℕ), B ≤ k →
      (3 / 10 : ℚ) ^ B ≤ Prσ β₀ k (fun β => PowNear E (terrasA (parityOf β))) := by
  obtain ⟨B, hBpos, hB⟩ := powNear_walk E
  refine ⟨B, hBpos, fun β₀ k hk => ?_⟩
  rw [prσ_eq_sum, show k = (k - B) + B by omega, sum_split]
  calc (3 / 10 : ℚ) ^ B = ∑ β₁ ∈ blockChoices (k - B), wtβ β₁ * (3 / 10 : ℚ) ^ B := by
        rw [← sum_mul, sum_wt, one_mul]
    _ ≤ _ := by
        refine sum_le_sum (fun β₁ _ => mul_le_mul_of_nonneg_left ?_ (fam_wt_nonneg β₁))
        obtain ⟨j, hj, hpn⟩ := hB (terrasA (parityOf (β₀ ++ β₁)))
        have hmem := topTail_mem hj.le
        have hgood : PowNear E (terrasA (parityOf (β₀ ++ (β₁ ++ topTail B j)))) := by
          rw [← List.append_assoc, topTail_terrasA B j]
          exact hpn
        calc (3 / 10 : ℚ) ^ B ≤ wtβ (topTail B j) := topTail_wt hj.le
          _ = wtβ (topTail B j) *
              (if PowNear E (terrasA (parityOf (β₀ ++ (β₁ ++ topTail B j)))) then 1 else 0) := by
              simp only [hgood, ↓reduceIte, mul_one]
          _ ≤ ∑ β₂ ∈ blockChoices B, wtβ β₂ *
              (if PowNear E (terrasA (parityOf (β₀ ++ (β₁ ++ β₂)))) then 1 else 0) :=
              single_le_sum (f := fun β₂ => wtβ β₂ *
                (if PowNear E (terrasA (parityOf (β₀ ++ (β₁ ++ β₂)))) then (1 : ℚ) else 0))
                (fun β₂ _ => mul_nonneg (fam_wt_nonneg β₂) (by split_ifs <;> norm_num)) hmem

/-! ## §5 The main theorem -/

/-- **The event (ii)** (Proposition 12.19): for the length `E` of the top window there are `c > 0` and `B`, depending only on `E`, such that if the first
blocks `β₀` are fixed and the remaining `k ≥ B` blocks are random, then with probability at least `c`, for **all** top windows `τ` of length `E` and
**all** `n`, `u` of the family (`K + s' ≤ n`, `u < 2^{n-K-s'}`, `K = E + 9`), the top window of the end point `x₁` is `τ`.
`c = (3/10)^B`. -/
theorem top_window (E : ℕ) : ∃ c : ℚ, 0 < c ∧ ∃ B : ℕ, ∀ (β₀ : List Bool) (k : ℕ), B ≤ k →
    c ≤ Prσ β₀ k (fun β => ∀ τ : List (Fin 2), τ.length = E → ∀ n u : ℕ,
      E + 9 + (parityOf β₀).length ≤ n → u < 2 ^ (n - (E + 9) - (parityOf β₀).length) →
      (binWord (famX1 β₀ β n (E + 9) (topT0 τ) u)).take E = τ) := by
  obtain ⟨B, -, hB⟩ := powNear_prob E
  refine ⟨(3 / 10 : ℚ) ^ B, by positivity, B, fun β₀ k hk => ?_⟩
  refine le_trans (hB β₀ k hk) (Prσ_mono β₀ k (fun β _ hβ => ?_))
  intro τ hτ n u hKn hu
  exact top_of_powNear τ hτ hKn hu hβ

end Collatz.Arctic.NatQ5.W3b
