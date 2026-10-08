/-
# Natural-number matrix interpretations ($\mathcal T$): non-vacuity checks for Section 11.2 of the paper (outside the closure)

The hypotheses of the main theorems of `H2Bin.lean`, `H2Chain.lean` and `H2Orbit.lean` can be satisfied, and their values at small numbers.
Computations use `decide +kernel` (reduction in the kernel; `native_decide` is not used). Only small numbers are used.
The values of the examples were compared with a Python computation independent of Lean (not part of this bundle).
-/
import CollatzProof.Arctic.Nat.H2Chain
import CollatzProof.Arctic.Nat.H2Orbit

namespace Collatz.Arctic.NatQ5.W2a.NonVacuity

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W2a

/-! ## §1 Words and numbers -/

/-- Splitting into three parts: `173 = 5·2^5 + 3·2^2 + 1`, so `bin'(173) = bin'(5) ++ 011 ++ 01`. -/
example : binWord 173 = binWord 5 ++ bitsF 3 3 ++ bitsF 2 1 := by decide +kernel

example : binWord (5 * 2 ^ (2 + 3) + 3 * 2 ^ 2 + 1) = binWord 5 ++ bitsF 3 3 ++ bitsF 2 1 :=
  binWord_split 5 3 1 2 3 (by norm_num) (by norm_num) (by norm_num)

/-- `1/3 = 0.0101…`. -/
example : dig 1 3 0 4 = [0, 1, 0, 1] := by decide +kernel

/-- `11/27 = 0.0110100…`: the 6 digits from position 0 are 3 windows of length 2. -/
example : dig 11 27 0 6 = dig 11 27 0 2 ++ dig 11 27 2 2 ++ dig 11 27 4 2 := by decide +kernel

example : binWord (valW 1 [1, 0, 1]) = [1, 0, 1] := binWord_valW _

/-! ## §2 Facts on powers of 2 modulo powers of 3 -/

/-- `ord_{27} 2 = 18` (the hypotheses of the theorem can be satisfied). -/
example : orderOf (2 : ZMod (3 ^ 3)) = 18 := orderOf_two_three_pow 3 (by norm_num)

example : 2 ^ 18 % 27 = 1 ∧ 2 ^ 9 % 27 ≠ 1 ∧ 2 ^ 6 % 27 ≠ 1 := by decide +kernel

/-- The powers of `4 = 1 + 3` cover `1 + 3ℤ` modulo 27 (`t < 9`). -/
example : ∀ x < 27, x % 3 = 1 → ∃ t < 9, 4 ^ t % 27 = x := by decide +kernel

example : ∃ e < 2 * 3 ^ 2, 3 ^ (2 + 1) ∣ 2 ^ e * 5 + 1 :=
  exists_two_pow_mul_add_one_dvd 2 5 (by norm_num)

example : ∃ e < 18, (2 ^ e * 5 + 1) % 27 = 0 := by decide +kernel

example : padicValNat 3 (4 ^ 9 - 1) = 3 := by
  rw [v3_four_pow_sub_one (by norm_num)]
  rw [show (9 : ℕ) = 3 ^ 2 by norm_num, padicValNat.prime_pow]

/-! ## §3 Backward chains (Lemma 11.5 of the paper) -/

/-- One step from `y = 7 = 3·2 + 1` (`U = 3`, `Θ = 1`, `ℓ = 1`): `n = 37`, `T^4(37) = 7`. -/
example : Collatz.Arctic.T^[4] 37 = 7 := by decide +kernel

example : ∃ n M V' : ℕ, M ≤ 4 * 1 ∧
      n = 3 / 3 ^ 1 * 2 ^ (0 + M + 1) + (1 + 2 ^ 1 * (3 % 3 ^ 1)) / 3 ^ 1 * 2 ^ (0 + M) + V' ∧
      (1 + 2 ^ 1 * (3 % 3 ^ 1)) / 3 ^ 1 < 2 ^ 1 ∧ V' < 2 ^ (0 + M) ∧ ¬ 3 ∣ n ∧
      Collatz.Arctic.T^[M] n = 3 * 2 ^ (0 + 1) + 1 * 2 ^ 0 + 0 ∧ ∀ i < M, 2 ≤ Collatz.Arctic.T^[i] n :=
  back_chain 1 3 1 0 0 1 (by norm_num) (by norm_num) (by norm_num) (by decide)

/-- **A concrete example for Lemmas 11.5 and 11.6 of the paper** (`p` empty, `w = 10`, `s` empty, `A = 2`, `k = 2A = 4`): `U = val(1 w^4) = 426`,
`X_0 = 3·1 + 2 = 5` (`v_3 = 0`), `E = 426 mod 9 = 3`, `ν = 2 + 3·3 = 11`, `θ_A = 11/27` (in lowest terms, `α = 3 ≥ A`).
`m = 1`: `y = val(1 w^5) = 1706`, `n = 6065`, `M = 5`, `bin'(6065) = bin'(⌊426/9⌋) ++ dig 11 27 0 2 ++ bitsF 5 17`. -/
example : valW 1 (wpow [1, 0] 4) = 426 ∧ valW 1 (wpow [1, 0] 4 ++ wpow [1, 0] 1) = 1706 ∧
    binWord 6065 = binWord (426 / 3 ^ 2) ++ dig 11 27 0 2 ++ bitsF 5 17 ∧
    Collatz.Arctic.T^[5] 6065 = 1706 ∧ ¬ 3 ∣ 6065 := by decide +kernel

/-- `m = 2`: `y = 6826`, `n = 6067`, `M = 3` (`n < y`; the number of steps of the chain changes with `m`, but is at most `4A`). -/
example : valW 1 (wpow [1, 0] 4 ++ wpow [1, 0] 2) = 6826 ∧
    binWord 6067 = binWord (426 / 3 ^ 2) ++ dig 11 27 0 4 ++ bitsF 3 3 ∧
    Collatz.Arctic.T^[3] 6067 = 6826 := by decide +kernel

/-- The hypotheses of `back_chain_word` can be satisfied (the setting of the examples above). -/
example : ∃ N D α D'' : ℕ, N.Coprime D ∧ 0 < N ∧ N < D ∧ D = 3 ^ α * D'' ∧ ¬ 3 ∣ D'' ∧
      D'' ∣ 2 ^ [1, 0].length - 1 ∧
      2 - padicValNat 3 ((2 ^ [1, 0].length - 1) * valW 1 ([] : List (Fin 2)) + valW 0 [1, 0]) ≤ α ∧
      ∀ m : ℕ, ¬ 3 ∣ valW 1 ([] ++ wpow [1, 0] 4 ++ wpow [1, 0] m ++ []) →
        ∃ n M V' : ℕ, M ≤ 4 * 2 ∧ V' < 2 ^ (([] : List (Fin 2)).length + M) ∧
          binWord n = binWord (valW 1 ([] ++ wpow [1, 0] 4) / 3 ^ 2) ++ dig N D 0 ([1, 0].length * m) ++
            bitsF (([] : List (Fin 2)).length + M) V' ∧
          ¬ 3 ∣ n ∧ Collatz.Arctic.T^[M] n = valW 1 ([] ++ wpow [1, 0] 4 ++ wpow [1, 0] m ++ []) ∧
          ∀ i < M, 2 ≤ Collatz.Arctic.T^[i] n := by
  have hA : padicValNat 3 ((2 ^ [1, 0].length - 1) * valW 1 ([] : List (Fin 2)) + valW 0 [1, 0]) < 2 := by
    have : (2 ^ [1, 0].length - 1) * valW 1 ([] : List (Fin 2)) + valW 0 [1, 0] = 5 := by decide +kernel
    rw [this, padicValNat.eq_zero_of_not_dvd (by norm_num)]; norm_num
  exact back_chain_word [] [1, 0] [] 4 2 (by decide) (three_pow_le_valW_wpow [] [1, 0] 2 (by decide)) hA

/-! ## §4 Frequencies of aligned segments (Lemma 11.7 of the paper) -/

/-- `1/9 = 0.000111…` (`α = 2`, `D'' = 1`, `L = 1`, `κ = 1`): 6 of the first 12 digits are 0. -/
example : ((Finset.range 12).filter (fun i => winVal 1 9 1 i = 0)).card = 6 := by decide +kernel

/-- The hypotheses of `win_count` can be satisfied (`N/D = 1/9`, `κ = L = 1`, `c = 1`, `P = 6`). -/
example (n v : ℕ) :=
  win_count (N := 1) (D := 9) (α := 2) (D'' := 1) (L := 1) (κ := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) le_rfl le_rfl n v

/-- An example in which the bound is not trivial: `N/D = 1/243` (`α = 5`), `κ = 2`, `L = 1`, `c = 1`, `P = 162`. For `n = 486` the number of windows
with each value is at most `(486 + 162)(1/4 + 1/81) = 170 + 2/3` (the trivial bound is 486). In fact there are 120, 126, 120, 120 windows with the values 0, 1, 2, 3. -/
example : ((Finset.range 486).filter (fun i => winVal 1 243 2 i = 1)).card = 126 := by decide +kernel

example :=
  win_count (N := 1) (D := 243) (α := 5) (D'' := 1) (L := 1) (κ := 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) le_rfl (by norm_num) 486 1

/-- The hypotheses of `win_freq` can be satisfied (`f ≡ 1`). -/
example (n : ℕ) :=
  win_freq (N := 1) (D := 9) (α := 2) (D'' := 1) (L := 1) (κ := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) le_rfl le_rfl (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) n

end Collatz.Arctic.NatQ5.W2a.NonVacuity
