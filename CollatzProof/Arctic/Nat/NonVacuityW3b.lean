/-
# Natural-number matrix interpretations ($\mathcal T$): non-vacuity checks for the top window and the chains of groups (Sections 12.5 and 12.7)

We check with concrete numbers that the premises of the main theorems of `W3Top.lean`, `W3Gap.lean` and `W3GapTail.lean` can be satisfied and that the events in
the conclusions are not trivial (they occur in some cases and not in others). Computational proofs use `decide +kernel` (no axioms are added) and `norm_num`.
`native_decide` is not used.

* **The event (PN)** (Proposition 12.19): `PowNear 4 12` (`3^12 = 531441`, `2^19 = 524288`, ratio `1.0137 < 1 + 2^{-6}`) and `¬ PowNear 4 5`
  (`3^5 = 243` is not within a factor `1 + 2^{-6}` of any power of 2). For the choice of blocks `X'Y'` (`A = 12` odd steps) the top window of the end point
  is `τ` (`ex_top_good`, from `top_of_powNear`). For `X'` alone (`A = 5`), with `τ = 0000` the top window of the end point
  is `1110`, not `τ` (`ex_top_bad`). So the event of `top_window` does not occur trivially.
* **Hits of groups**: with group size `g = 0 + 1` (no mixing part; the cut, which is the target, is a single block), the cut word of `X'` is
  the 8 digits `11111001` of `r_{X'} = 249` (`ex_cut_X`). It contains the word `01` (a hit, `ex_hit`) and does not contain the word `010`
  (a miss, `ex_miss`). So `GHit` is not a trivial event.
* **The premises can be satisfied**: concrete examples of the premises of `gap_chain_infix` (`v < 2^ℓ`, `ℓ ≤ 8a`) and of `tail_small` and `gap_twin` (polynomial
  weights and a linear look-back). The chain bound `(1 - 2^{-ℓ-1})^K` is less than 1 for `K ≥ 1` (`ex_chain_lt_one`).
-/
import CollatzProof.Arctic.Nat.W3Top
import CollatzProof.Arctic.Nat.W3GapTail

namespace Collatz.Arctic.NatQ5.W3b.Example

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W2a Collatz.Arctic.NatQ5.W3b

/-! ## §1 The event (PN) -/

theorem ex_powNear : PowNear 4 12 := ⟨19, by norm_num, by norm_num⟩

theorem ex_not_powNear : ¬ PowNear 4 5 := by
  rintro ⟨e, h1, h2⟩
  rcases Nat.lt_or_ge e 8 with he | he
  · have : 2 ^ e ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h2
    omega
  · have : 2 ^ 8 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    norm_num at h1
    omega

theorem ex_terrasA_XY : terrasA (parityOf [true, false]) = 12 := by
  rw [terrasA_eq]; decide +kernel

theorem ex_terrasA_X : terrasA (parityOf [true]) = 5 := by
  rw [terrasA_eq]; decide +kernel

/-- `X'Y'` (`A = 12`): for every `τ` of length 4, with `n = 13` and `u = 0` the top window of the end point is `τ`. -/
theorem ex_top_good (τ : List (Fin 2)) (hτ : τ.length = 4) :
    (binWord (famX1 [] [true, false] 13 (4 + 9) (topT0 τ) 0)).take 4 = τ := by
  refine top_of_powNear τ hτ (by decide) (by decide) ?_
  rw [ex_terrasA_XY]; exact ex_powNear

theorem ex_famRho_nil (β : List Bool) : famRho [] β = 0 := by
  have := fam_rho_lt [] β
  have e : (parityOf []).length = 0 := by simp [parityOf]
  rw [e, pow_zero] at this
  omega

/-- `X'` alone (`A = 5`): with `τ = 0000` the top window of the end point is `1110` (not `τ`). -/
theorem ex_top_bad :
    (binWord (famX1 [] [true] 13 (4 + 9) (topT0 [0, 0, 0, 0]) 0)).take 4 = [1, 1, 1, 0] := by
  have hT0 : topT0 [0, 0, 0, 0] = 4096 := by decide +kernel
  have hx : famX1 [] [true] 13 (4 + 9) (topT0 [0, 0, 0, 0]) 0
      = terrasC (parityOf [true]) + 243 * 4096 := by
    unfold famX1 famT
    rw [hT0, ex_famRho_nil, ex_terrasA_X]
    norm_num
  have hc : terrasC (parityOf [true]) < 243 := by
    have := terrasC_lt (parityOf [true])
    rwa [ex_terrasA_X] at this
  have hlo : 2 ^ 15 * (2 ^ 4 + 14) ≤ famX1 [] [true] 13 (4 + 9) (topT0 [0, 0, 0, 0]) 0 := by
    rw [hx]
    generalize terrasC (parityOf [true]) = c at hc ⊢
    omega
  have hhi : famX1 [] [true] 13 (4 + 9) (topT0 [0, 0, 0, 0]) 0 < 2 ^ 15 * (2 ^ 4 + 14 + 1) := by
    rw [hx]
    generalize terrasC (parityOf [true]) = c at hc ⊢
    omega
  have h := take_binWord_of_bounds (N := 15) (E := 4) (θ := 14) (by norm_num) hlo hhi
  rw [h]
  decide +kernel

theorem ex_top_bad_ne :
    (binWord (famX1 [] [true] 13 (4 + 9) (topT0 [0, 0, 0, 0]) 0)).take 4 ≠ [0, 0, 0, 0] := by
  rw [ex_top_bad]; decide

/-! ## §2 Hits of groups -/

/-- The cut word of `X'` is the 8 digits `11111001` of `r_{X'} = 249`. -/
theorem ex_cut_X : cutWord 1 [true] 0 =
    [Letter.t, Letter.t, Letter.t, Letter.t, Letter.t, Letter.f, Letter.f, Letter.t] := by
  decide +kernel

theorem ex_hit : GHit (fun w => bitsMSB 2 1 <:+: w) 0 0 1 0 [true] := by
  unfold GHit
  decide +kernel

theorem ex_miss : ¬ GHit (fun w => bitsMSB 3 2 <:+: w) 0 0 1 0 [true] := by
  unfold GHit
  decide +kernel

/-! ## §3 The premises can be satisfied -/

/-- An example of the premises of `gap_chain_infix` (`ℓ = 2`, `v = 1`, `a = 1`). -/
theorem ex_gap_chain :
    ∃ n₀ : ℕ, ∀ n₁ ≥ n₀, ∀ (β₀ : List Bool) (k j K : ℕ), (j + K) * (n₁ + 1) ≤ k →
      Prσ β₀ k (AllMiss (fun w => bitsMSB 2 1 <:+: w) β₀.length n₁ 1 j K) ≤
        (1 - 1 / 2 ^ (2 + 1)) ^ K :=
  gap_chain_infix 2 1 1 (by norm_num) (by norm_num)

theorem ex_chain_lt_one (ℓ K : ℕ) (hK : 1 ≤ K) : (1 - 1 / (2 : ℚ) ^ (ℓ + 1)) ^ K < 1 := by
  have h0 : (0 : ℚ) ≤ 1 - 1 / 2 ^ (ℓ + 1) := by
    have : (1 : ℚ) / 2 ^ (ℓ + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    linarith
  have h1 : 1 - 1 / (2 : ℚ) ^ (ℓ + 1) < 1 := by
    have : (0 : ℚ) < 1 / 2 ^ (ℓ + 1) := by positivity
    linarith
  exact pow_lt_one₀ h0 h1 (by omega)

/-- An example of the premises of `tail_small`: `C = 1`, `d = 2`, `A R = R`, `K R = ⌈R/3⌉`, `q = 1/2`. -/
theorem ex_tail :
    ∀ ε : ℚ, 0 < ε → ∃ J : ℕ, ∀ S : Finset ℕ, (∀ R ∈ S, J < R) →
      ∑ R ∈ S, (1 : ℚ) * ((R : ℚ) + 1) ^ 2 * (((R : ℕ) + 1) * (1 / 2) ^ ((R + 2) / 3)) ≤ ε :=
  tail_small 1 (by norm_num) 2 1 0 (by norm_num) le_rfl 3 0 (by norm_num) (1 / 2) (by norm_num)
    (by norm_num) (fun R => R) (fun R => (R + 2) / 3) (fun R => by simp) (fun R => by omega)

end Collatz.Arctic.NatQ5.W3b.Example
