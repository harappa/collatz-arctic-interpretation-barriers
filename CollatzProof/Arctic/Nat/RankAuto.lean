/-
# Ranking functions computed by automata over ℕ (Corollary 10.13 of the paper, revision r4; cf. Theorem 3.6)

Suggested by an external review of revision r3 (3.1). No value automaton `(u, N₀, N₁, c)` with natural-number weights
(any dimension, ordinary sum and product, `V(n) = u^T N_{bin'(n)} c`) has `V(T n) + 1 ≤ V(n)` for every `n ≥ 2`; the
same holds reading the digits from the least significant end (`V(n) = u^T N_{b_k} ⋯ N_{b_1} c`), by transposing `N_b`.

* Proof: the decrease gives (M) (`AutoMono`). The value-level core (Theorem 10.11 (i), `AutoValueCoreNoG2`) for the rule
  `f. → .` gives `n, m` with the orbit segment `n, …, T^{m-1} n` at least 2 and `V(n) < #_{f.→.}(n, m)`. But
  `V(n) ≥ m + V(T^m n) ≥ m`, and `f. → .` is used at most once per canonical derivation (`fam_uses_even`), so
  `#_{f.→.}(n, m) ≤ m`. A contradiction.
* No hypothesis (P) is needed, but the decrease is required at every `n ≥ 2` (Theorem 10.11 assumes (M) for every
  `n ≥ 2`). For functions that only do not increase, (P) cannot be dropped (the remark after Proposition 9.5).

-/
import CollatzProof.Arctic.Nat.H2MainExtra
import CollatzProof.Arctic.FamilyUses

namespace Collatz.Arctic.NatQ5.Rank

open Collatz.Arctic Collatz.Arctic.NatQ5 Matrix

/-- `f. → .` is used at most once in each canonical derivation. -/
theorem uses_fdot_le_one (n : ℕ) : uses ⟨[Letter.f, Letter.rgt], [Letter.rgt]⟩ n ≤ 1 := by
  rw [fam_uses_even]
  split_ifs <;> omega

/-- The uses of `f. → .` along an orbit segment are at most its length. -/
theorem usesOrbit_fdot_le (n m : ℕ) : usesOrbit ⟨[Letter.f, Letter.rgt], [Letter.rgt]⟩ n m ≤ m := by
  unfold usesOrbit
  have h := List.sum_le_length_nsmul ((List.range m).map fun i => uses ⟨[Letter.f, Letter.rgt], [Letter.rgt]⟩ (T^[i] n)) 1
    (fun x hx => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact uses_fdot_le_one _)
  simpa using h

section
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- A decrease by at least 1 at each step gives a decrease by the length of the segment. -/
theorem aval_iter_le (A : ValAuto Q) (hdec : ∀ n, 2 ≤ n → aval A (binWord (T n)) + 1 ≤ aval A (binWord n)) :
    ∀ m n, (∀ i < m, 2 ≤ T^[i] n) → aval A (binWord (T^[m] n)) + m ≤ aval A (binWord n)
  | 0, n, _ => by simp
  | m + 1, n, h => by
    have h0 : 2 ≤ n := by simpa using h 0 (Nat.succ_pos m)
    have ih := aval_iter_le A hdec m (T n) fun i hi => by
      have := h (i + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    rw [Function.iterate_succ_apply]
    have := hdec n h0
    omega

/-- The transposed automaton (`N_b` transposed, `u` and `c` exchanged). -/
def transposeAuto (A : ValAuto Q) : ValAuto Q := ⟨fun b => (A.B b)ᵀ, A.v, A.u⟩

/-- The value of the transposed automaton, read from the most significant end, is the value of the original automaton read from the least significant end. -/
theorem aval_transposeAuto (A : ValAuto Q) (ω : List (Fin 2)) :
    aval (transposeAuto A) ω = aval A ω.reverse := by
  have hprod : Rigid.DxN (fun b => (A.B b)ᵀ) ω = (Rigid.DxN A.B ω.reverse)ᵀ := by
    unfold Rigid.DxN
    rw [Matrix.transpose_list_prod, List.map_reverse, List.map_reverse, List.reverse_reverse, List.map_map]
    rfl
  unfold aval transposeAuto
  simp only
  rw [hprod, mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]

end

/-- **Corollary 10.13 (reading from the most significant end)**: no value automaton with natural-number weights has
values `V` with `V(T n) + 1 ≤ V(n)` for every `n ≥ 2`. -/
theorem noRankAuto : ¬ ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (A : ValAuto Q),
    ∀ n, 2 ≤ n → aval A (binWord (T n)) + 1 ≤ aval A (binWord n) := by
  rintro ⟨Q, _, _, A, hdec⟩
  have hmono : AutoMono A := fun n hn => by have := hdec n hn; omega
  obtain ⟨n, -, m, hstay, hlt⟩ := autoValueCore_iff_noG2.mp W4a.autoValueCore Q A hmono
    ⟨[Letter.f, Letter.rgt], [Letter.rgt]⟩ (by decide) 0
  have h1 := aval_iter_le A hdec m n hstay
  have h2 := usesOrbit_fdot_le n m
  omega

/-- **Corollary 10.13 (reading from the least significant end)**: `V(n) = u^T N_{b_k} ⋯ N_{b_1} c` (`b_1 ⋯ b_k = bin'(n)`)
never satisfies `V(T n) + 1 ≤ V(n)` for every `n ≥ 2`. -/
theorem noRankAuto_lsb : ¬ ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (A : ValAuto Q),
    ∀ n, 2 ≤ n → aval A (binWord (T n)).reverse + 1 ≤ aval A (binWord n).reverse := by
  rintro ⟨Q, _, _, A, hdec⟩
  exact noRankAuto ⟨Q, inferInstance, inferInstance, transposeAuto A, fun n hn => by
    rw [aval_transposeAuto, aval_transposeAuto]; exact hdec n hn⟩

end Collatz.Arctic.NatQ5.Rank
