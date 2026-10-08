/-
# Natural-number matrix interpretations ($\mathcal T$): non-vacuity checks for Section 11.4 of the paper (outside the closure)

The hypotheses of the main theorems of `H2Shrink.lean` can be satisfied, and their values at small numbers. Computations use `decide +kernel` (reduction in the kernel;
`native_decide` is not used). Only small numbers are used. The values of the examples were compared with a Python computation independent of Lean
(standard library only; not part of this bundle).

* §1 Shrinking chains: `T^3(7) = 26`, `T^6(35) = 5` (`j = 2`, `e = 4`, `z = 9`). The comparison of lengths holds with equality.
* §2 The form of the values: `Ψ = 0`, `h = 3` (`S = 21`, `μ = 64`, `δ = 42`).
* §3 A small example from end to end: `ε = 111`, `y = 699050`, `3^5 ∣ 2^2 y + 1`, `n = 552335`, `T^6(n) = y`.
* §4 The hypotheses of `shrink_target` can be satisfied (`Ψ = 0`, `h = 3`, `p₀ = s = []`: `Y_r = 2^{6r+1}`).
* §5 `shrink_contra` has teeth: `V(n) := [3 ∤ n] 2^{ℓ'(n)}` with `G = 2` satisfies all hypotheses except `hT`, so
  the theorem shows that `hT` fails (indeed `V(T 5) = 8 > 4 = V(5)`). `V = 0` satisfies `hT`, `h3` and `hup`, and only `hlow` fails.
* §6 The condition `1 < G` of `not_exp_le_poly` is needed (for `G = 1` the inequality holds).
-/
import CollatzProof.Arctic.Nat.H2Shrink

namespace Collatz.Arctic.NatQ5.W2d.NonVacuity

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W2a Collatz.Arctic.NatQ5.W2d

/-! ## §1 Shrinking chains -/

/-- `T^3(2^3 - 1) = 3^3 - 1`: `7 → 11 → 17 → 26`. -/
example : Collatz.Arctic.T^[3] 7 = 26 := by decide +kernel

example : Collatz.Arctic.T^[3] (2 ^ 3 * 1 - 1) = 3 ^ 3 * 1 - 1 := shrink_iterate 3 1 le_rfl

/-- `j = 2`, `e = 4`, `y = 5`, `z = 9` (`9·9 = 2^4·5 + 1`), `n = 35`: `35 → 53 → 80 → 40 → 20 → 10 → 5`. -/
example : Collatz.Arctic.T^[6] 35 = 5 := by decide +kernel

example : Collatz.Arctic.T^[2 + 4] (2 ^ 2 * 9 - 1) = 5 ∧
    ∀ i < 2 + 4, 2 ≤ Collatz.Arctic.T^[i] (2 ^ 2 * 9 - 1) :=
  shrink_chain (by norm_num) (by norm_num) (by norm_num)

/-- `3^{j+1} = 27 ∣ 81`, so `3 ∣ z`, and the starting point `35` is not a multiple of 3. -/
example : ¬ 3 ∣ 2 ^ 2 * 9 - 1 := shrink_not_dvd ⟨3, rfl⟩ (by norm_num)

/-- Comparison of lengths (`j' = 1`): `ℓ'(35) + 1 = 6 ≤ 6 = ℓ'(5) + 4`. It holds with equality. -/
example : (binWord 35).length + 1 = (binWord 5).length + 4 := by decide +kernel

example : (binWord (2 ^ (2 * 1) * 9 - 1)).length + 1 ≤ (binWord 5).length + 4 :=
  shrink_length (by norm_num) (by norm_num) (by norm_num)

/-! ## §2 The form of the values -/

example : sBlock [0] 3 = 21 := by decide +kernel

/-- `val(π₁) - val(π₀) = S`: `π₀ = 000000`, `π₁ = 010101` (`21`). -/
example : valW 0 (Rigid.piBlock [0] 3 1) = valW 0 (Rigid.piBlock [0] 3 0) + 21 := by decide +kernel

/-- `y(111) = Y_3 + δ (μ² + μ + 1)`: `699050 = 524288 + 42·4161`. -/
example : valW 1 ([] ++ Rigid.heavyWord [0] 3 [1, 1, 1] ++ []) = 699050 := by decide +kernel

example : valW 1 ([] ++ Rigid.heavyWord [0] 3 [0, 0, 0] ++ []) = 524288 := by decide +kernel

example : valW 1 ([] ++ Rigid.heavyWord [0] 3 [1, 1, 1] ++ []) =
    valW 1 ([] ++ Rigid.heavyWord [0] 3 (List.replicate 3 0) ++ []) +
      sBlock [0] 3 * 2 ^ (1 + 0) * valB (2 ^ (3 * (1 + 1))) 0 [1, 1, 1] :=
  heavy_val [] [] [0] 3 [1, 1, 1]

example : valB 64 0 [1, 1, 1] = 4161 := by decide +kernel

/-- The indicator word: for `J = {0, 2}` and `r = 4`, `ε = 0101` (`ε_i = [3 - i ∈ J]`), and `valB 64 0 ε = 64² + 1`. -/
example : epsOf {0, 2} 4 = [0, 1, 0, 1] := by decide +kernel

example : valB 64 0 (epsOf {0, 2} 4) = 64 ^ 0 + 64 ^ 2 := by decide +kernel

/-! ## §3 A small example from end to end (hitting the class `ξ = 0` and a shrinking chain) -/

/-- `ε = 111`, `y = 699050`, `j = 4`, `e = 2`: `3^5 = 243 ∣ 2^2 y + 1 = 2796201`. -/
example : 3 ^ (4 + 1) ∣ 2 ^ 2 * 699050 + 1 := by decide +kernel

/-- `z = 34521 = 3·11507`, `n = 2^4 z - 1 = 552335`, `T^6(n) = y`, and `n` is not a multiple of 3. -/
example : Collatz.Arctic.T^[4 + 2] (2 ^ 4 * 34521 - 1) = 699050 ∧
    ∀ i < 4 + 2, 2 ≤ Collatz.Arctic.T^[i] (2 ^ 4 * 34521 - 1) :=
  shrink_chain (by norm_num) (by norm_num) (by norm_num)

example : Collatz.Arctic.T^[6] 552335 = 699050 := by decide +kernel

example : ¬ 3 ∣ 552335 := by decide

/-- Lengths (`j' = 2`): `ℓ'(n) + 2 = 21 = ℓ'(y) + 2`. It holds with equality. -/
example : (binWord 552335).length + 2 = (binWord 699050).length + 2 ∧ (binWord 699050).length = 19 := by
  decide +kernel

/-! ## §4 The hypotheses of `shrink_target` can be satisfied -/

theorem valW_zero_of_forall {w : List (Fin 2)} (hw : ∀ x ∈ w, x = 0) : valW 0 w = 0 := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [valW_cons, hw b List.mem_cons_self]
    simpa using ih fun x hx => hw x (List.mem_cons_of_mem _ hx)

theorem mem_piBlock {Ψ : List (Fin 2)} {h : ℕ} {e x : Fin 2} (hx : x ∈ Rigid.piBlock Ψ h e) :
    x ∈ Ψ ∨ x = e := by
  unfold Rigid.piBlock at hx
  obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
  rw [(List.mem_replicate.1 hl).2] at hxl
  simpa using hxl

theorem mem_heavyWord {Ψ : List (Fin 2)} {h : ℕ} {ε : List (Fin 2)} {x : Fin 2}
    (hx : x ∈ Rigid.heavyWord Ψ h ε) : x ∈ Ψ ∨ x ∈ ε := by
  unfold Rigid.heavyWord at hx
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hl
    rcases mem_piBlock hxl with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (h1 ▸ he)
  · exact Or.inl hx

theorem heavyWord_zero_mem {r : ℕ} {x : Fin 2} (hx : x ∈ Rigid.heavyWord [0] 3 (List.replicate r 0)) : x = 0 := by
  rcases mem_heavyWord hx with h | h
  · simpa using h
  · exact (List.mem_replicate.1 h).2

/-- `Y_r = val(1 (00)^{3r} 0) = 2^{6r+1} ≡ 2 (mod 3)`. -/
theorem Y_mod (r : ℕ) : valW 1 ([] ++ Rigid.heavyWord [0] 3 (List.replicate r 0) ++ []) % 3 = 2 := by
  simp only [List.nil_append, List.append_nil]
  rw [valW_one, valW_zero_of_forall fun x hx => heavyWord_zero_mem hx, Rigid.heavyWord_length,
    List.length_replicate, add_zero, two_pow_mod_three]
  simp only [List.length_singleton]
  split_ifs with hh
  · omega
  · rfl

theorem hY_ex : ∀ r, ¬ 3 ∣ valW 1 ([] ++ Rigid.heavyWord [0] 3 (List.replicate r 0) ++ []) := by
  intro r h
  have := Y_mod r
  omega

/-- `shrink_target` applies to the family `Ψ = 0`, `h = 3`, `p₀ = s = []`. -/
example : ∃ E K₀ : ℕ, ∀ j' : ℕ, ∃ (ε : List (Fin 2)) (n m : ℕ),
    ([] ++ Rigid.heavyWord [0] 3 ε ++ []).length ≤ K₀ * (j' + 1) ^ 2 ∧
    1 ≤ n ∧ ¬ 3 ∣ n ∧
    Collatz.Arctic.T^[m] n = valW 1 ([] ++ Rigid.heavyWord [0] 3 ε ++ []) ∧
    (∀ i < m, 2 ≤ Collatz.Arctic.T^[i] n) ∧
    (binWord n).length + j' ≤ ([] ++ Rigid.heavyWord [0] 3 ε ++ []).length + E :=
  shrink_target [0] [] [] (by norm_num) hY_ex

/-- Every value of this family is `≡ 2 (mod 3)` (`δ = 42` is a multiple of 3). -/
theorem y_mod (ε : List (Fin 2)) : valW 1 ([] ++ Rigid.heavyWord [0] 3 ε ++ []) % 3 = 2 := by
  have key : ∀ Y X B : ℕ, Y % 3 = 2 → (Y + 3 * 7 * X * B) % 3 = 2 := by
    intro Y X B h
    rw [show 3 * 7 * X * B = 3 * (7 * X * B) by ring, Nat.add_mul_mod_self_left]
    exact h
  rw [heavy_val, show sBlock [0] 3 = 3 * 7 by decide +kernel]
  exact key _ _ _ (Y_mod _)

/-! ## §5 `shrink_contra` has teeth -/

/-- `V(n) := [3 ∤ n] 2^{ℓ'(n)}`. -/
noncomputable def Vex (n : ℕ) : ℝ := if 3 ∣ n then 0 else (2 : ℝ) ^ (binWord n).length

theorem Vex_h3 : ∀ n, 1 ≤ n → 3 ∣ n → Vex n ≤ 0 := by
  intro n _ h; simp [Vex, h]

theorem Vex_up : ∀ n, 1 ≤ n → ¬ 3 ∣ n →
    Vex n ≤ 1 * (((binWord n).length : ℝ) + 1) ^ 0 * (2 : ℝ) ^ (binWord n).length := by
  intro n _ h; simp [Vex, h]

theorem Vex_low : ∀ ε, 1 * (2 : ℝ) ^ (Rigid.heavyWord [0] 3 ε).length ≤
    Vex (valW 1 ([] ++ Rigid.heavyWord [0] 3 ε ++ [])) := by
  intro ε
  have h3 : ¬ 3 ∣ valW 1 ([] ++ Rigid.heavyWord [0] 3 ε ++ []) := by
    have := y_mod ε; omega
  simp only [List.nil_append, List.append_nil] at h3 ⊢
  simp [Vex, h3, binWord_valW]

/-- All hypotheses except `hT` hold, so `shrink_contra` shows that `hT` fails. -/
example : ¬ ∀ n, 2 ≤ n → ¬ 3 ∣ n → Vex (Collatz.Arctic.T n) ≤ Vex n := fun hT =>
  shrink_contra Vex [0] [] [] (h := 3) (by norm_num) (G := 2) (c := 1) (C := 1) (p := 0) (by norm_num)
    (by norm_num) hT Vex_h3 Vex_up Vex_low

/-- Indeed it fails at `n = 5`: `T 5 = 8`, `V(8) = 2^3 > 2^2 = V(5)`. -/
example : ¬ Vex (Collatz.Arctic.T 5) ≤ Vex 5 := by
  have hT5 : Collatz.Arctic.T 5 = 8 := by decide
  have h8 : (binWord 8).length = 3 := by decide +kernel
  have h5 : (binWord 5).length = 2 := by decide +kernel
  rw [hT5]
  simp only [Vex, h8, h5, show ¬ 3 ∣ 8 by decide, show ¬ 3 ∣ 5 by decide, ↓reduceIte]
  norm_num

/-- Conversely, `hT`, `h3` and `hup` alone can be satisfied (`V = 0`, `C = 0`). What fails is `hlow` (`c > 0`). -/
example : (∀ n, 2 ≤ n → ¬ 3 ∣ n → (fun _ : ℕ => (0 : ℝ)) (Collatz.Arctic.T n) ≤ (fun _ : ℕ => (0 : ℝ)) n) ∧
    (∀ n, 1 ≤ n → 3 ∣ n → (fun _ : ℕ => (0 : ℝ)) n ≤ 0) ∧
    (∀ n, 1 ≤ n → ¬ 3 ∣ n → (fun _ : ℕ => (0 : ℝ)) n ≤
      0 * (((binWord n).length : ℝ) + 1) ^ 0 * (2 : ℝ) ^ (binWord n).length) ∧
    ¬ (∀ ε, 1 * (2 : ℝ) ^ (Rigid.heavyWord [0] 3 ε).length ≤
      (fun _ : ℕ => (0 : ℝ)) (valW 1 ([] ++ Rigid.heavyWord [0] 3 ε ++ []))) := by
  refine ⟨fun _ _ _ => le_rfl, fun _ _ _ => le_rfl, fun _ _ _ => by simp, fun h => ?_⟩
  have := h []
  have : (0 : ℝ) < 1 * 2 ^ (Rigid.heavyWord [0] 3 []).length := by positivity
  linarith

/-! ## §6 The condition `1 < G` of `not_exp_le_poly` is needed -/

example : ∀ j : ℕ, (1 : ℝ) ^ j ≤ 1 * ((j : ℝ) + 1) ^ 0 := by intro j; simp

example : ¬ ∀ j : ℕ, (2 : ℝ) ^ j ≤ 1000 * ((j : ℝ) + 1) ^ 3 := not_exp_le_poly (by norm_num) 1000 3

end Collatz.Arctic.NatQ5.W2d.NonVacuity
