/-
Components of the formalization of Proposition 3.7 and Proposition 6.7 (iii) (quadratic use of the carry rules A): the family of the periodic point 1/5, and
quadratic use of all six carry rules A, `aRule_quad`.

* On the 2-adic rational 1/5, `T` has the cycle `1/5 → 4/5 → 2/5 → 1/5` of period 3 (odd, even, even).
  From a point with `5n = 1 + 8E` (`E ≥ 1`), three steps give `5 T³ n = 1 + 3E` (`T3_five`).
* **Family F** (`famF`): `5n = 1 + 8·4096^k·(5w + 3)` (`n ≡ 1/5 mod 2^(12k+3)`). After 12 steps (4 odd steps) it is in `famF k`.
  `y = (n-1)/2` satisfies `5y + 2 = 16^(3k+3)·(5(4w+2) + 2)` (`y ≡ -2/5`) and has `3k+3` copies of the period `0110` at the bottom.
  Starting from carry 2, the first period enters carry 1, and each later period uses `aRule 0 1`, `aRule 1 0`, `aRule 1 1`,
  `aRule 0 2` once each.
* The remaining two carry rules are handled by family Z (`aRule 0 0`) and family O (`aRule 1 2`) (`ARuleFamily.lean`).
-/
import CollatzProof.Arctic.ARuleFamily

namespace Collatz.Arctic.ARule

/-- Three steps (odd, even, even) from a point with `5n = 1 + 8E`: `5 T³ n = 1 + 3E`, with intermediate points at least 2. -/
lemma T3_five (n E : ℕ) (hE : 1 ≤ E) (h : 5 * n = 1 + 8 * E) :
    5 * T^[3] n = 1 + 3 * E ∧ ∀ i < 3, 2 ≤ T^[i] n := by
  have hn : n % 2 = 1 := by omega
  have e1 : 5 * T n = 4 + 12 * E := by rw [T_odd hn]; omega
  have hn1 : T n % 2 = 0 := by omega
  have e2 : 5 * T (T n) = 2 + 6 * E := by rw [T_even hn1]; omega
  have hn2 : T (T n) % 2 = 0 := by omega
  have e3 : 5 * T (T (T n)) = 1 + 3 * E := by rw [T_even hn2]; omega
  refine ⟨e3, ?_⟩
  intro i hi
  interval_cases i
  · show 2 ≤ n; omega
  · show 2 ≤ T n; omega
  · show 2 ≤ T (T n); omega

/-- Level `k` of family F: `5n = 1 + 8·4096^k·(5w + 3)`. -/
def famF (k n : ℕ) : Prop := ∃ w, 5 * n = 1 + 8 * (4096 ^ k * (5 * w + 3))

/-- Split `T^[12] x` into four blocks of 3 steps (chaining the equations as explicit terms; see the remark at `orbit_append'`). -/
lemma iter_12 (x : ℕ) : T^[12] x = T^[3] (T^[3] (T^[3] (T^[3] x))) :=
  (Function.iterate_add_apply T 9 3 x).trans ((Function.iterate_add_apply T 6 3 (T^[3] x)).trans
    (Function.iterate_add_apply T 3 3 (T^[3] (T^[3] x))))

lemma famF_step (k n : ℕ) (h : famF (k + 1) n) : famF k (T^[12] n) ∧ ∀ i < 12, 2 ≤ T^[i] n := by
  obtain ⟨w, hn⟩ := h
  set E0 := 4096 ^ k * (5 * w + 3) with hE0
  have hE0pos : 1 ≤ E0 := Nat.mul_pos (by positivity) (by omega)
  have h1 : 4096 ^ (k + 1) * (5 * w + 3) = 4096 * E0 := by rw [hE0, pow_succ]; ring
  rw [h1] at hn
  -- `omega` compares atoms with `isDefEq`, so do not call it while hypotheses containing different iterates `T^[3] …` are in the context
  have p1 : 1 ≤ 4096 * E0 := by omega
  have p2 : 1 ≤ 1536 * E0 := by omega
  have p3 : 1 ≤ 576 * E0 := by omega
  have p4 : 1 ≤ 216 * E0 := by omega
  obtain ⟨a1, o1⟩ := T3_five n (4096 * E0) p1 hn
  obtain ⟨a2, o2⟩ := T3_five (T^[3] n) (1536 * E0) p2 (by rw [a1]; ring)
  obtain ⟨a3, o3⟩ := T3_five (T^[3] (T^[3] n)) (576 * E0) p3 (by rw [a2]; ring)
  obtain ⟨a4, o4⟩ := T3_five (T^[3] (T^[3] (T^[3] n))) (216 * E0) p4 (by rw [a3]; ring)
  have e6 : T^[3 + 3] n = T^[3] (T^[3] n) := Function.iterate_add_apply T 3 3 n
  have e9 : T^[3 + 3 + 3] n = T^[3] (T^[3] (T^[3] n)) :=
    (Function.iterate_add_apply T 6 3 n).trans (Function.iterate_add_apply T 3 3 (T^[3] n))
  refine ⟨⟨81 * w + 48, ?_⟩, ?_⟩
  · have : 4096 ^ k * (5 * (81 * w + 48) + 3) = 81 * E0 := by rw [hE0]; ring
    rw [this, iter_12, a4]; ring
  · exact orbit_append' (orbit_append' (orbit_append' o1 rfl o2) e6 o3) e9 o4

lemma famF_use (ρ : Rule) (hρ : ρ ∈ patRules) (k n : ℕ) (h : famF (k + 1) n) : k ≤ uses ρ n := by
  obtain ⟨w, hn⟩ := h
  have hρ' : ∃ b d, ρ = aRule b d := by
    simp only [patRules, List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
  obtain ⟨b, d, rfl⟩ := hρ'
  set P := 4096 ^ (k + 1) with hP
  have hP16 : P = 16 ^ (3 * k + 3) := by
    rw [hP, show 3 * k + 3 = 3 * (k + 1) by ring, pow_mul]; norm_num
  have hn1 : n % 2 = 1 := by omega
  have hy : 5 * ((n - 1) / 2) + 2 = 16 ^ (3 * k + 3) * (5 * (4 * w + 2) + 2) := by
    rw [← hP16]
    have : P * (5 * (4 * w + 2) + 2) = 4 * (P * (5 * w + 3)) := by ring
    rw [this]; omega
  rw [uses_aRule_odd _ _ _ hn1, tailBitsLSB_pat _ _ _ (by omega) hy,
    show 3 * k + 3 = (3 * k + 2) + 1 by ring]
  -- The first period starts from carry 2: after `aRule 0 2`, `aRule 1 1`, `aRule 1 2`, `aRule 0 2`, the carry is 1
  have : sweepRules (pat (3 * k + 2 + 1) ++ tailBitsLSB (4 * w + 2)) 2 =
      aRule 0 2 :: aRule 1 1 :: aRule 1 2 :: aRule 0 2 ::
        sweepRules (pat (3 * k + 2) ++ tailBitsLSB (4 * w + 2)) 1 := rfl
  rw [this]
  have := count_sweep_pat (aRule b d) hρ (3 * k + 2) (tailBitsLSB (4 * w + 2))
  have h1 := count_le_cons (aRule b d) (aRule 0 2)
    (sweepRules (pat (3 * k + 2) ++ tailBitsLSB (4 * w + 2)) 1)
  have h2 := count_le_cons (aRule b d) (aRule 1 2) (aRule 0 2 ::
    sweepRules (pat (3 * k + 2) ++ tailBitsLSB (4 * w + 2)) 1)
  have h3 := count_le_cons (aRule b d) (aRule 1 1) (aRule 1 2 :: aRule 0 2 ::
    sweepRules (pat (3 * k + 2) ++ tailBitsLSB (4 * w + 2)) 1)
  have h4 := count_le_cons (aRule b d) (aRule 0 2) (aRule 1 1 :: aRule 1 2 :: aRule 0 2 ::
    sweepRules (pat (3 * k + 2) ++ tailBitsLSB (4 * w + 2)) 1)
  omega

lemma famF_ex (k : ℕ) : ∃ n, k ≤ n ∧ famF k n ∧ lenT n ≤ 12 * k + 12 := by
  set P := 4096 ^ k with hP
  have hP5 : P % 5 = 1 := by rw [hP, Nat.pow_mod]; norm_num
  have hPk : k < P := Nat.lt_pow_self (by norm_num)
  have h2 : 2 ^ (12 * k + 2 + 1) = 8 * P := by
    rw [hP, show 12 * k + 2 + 1 = 12 * k + 3 by ring, pow_add, pow_mul]; norm_num; ring
  refine ⟨(1 + 24 * P) / 5, by omega, ⟨0, by omega⟩, ?_⟩
  have := lenT_le_of_lt (n := (1 + 24 * P) / 5) (L := 12 * k + 2) (by rw [h2]; omega)
  omega

theorem quadF (ρ : Rule) (hρ : ρ ∈ patRules) (C N : ℕ) :
    ∃ n, N ≤ n ∧ ∃ m, (∀ i < m, 2 ≤ T^[i] n) ∧ C * (lenT n + 1) < usesOrbit ρ n m :=
  quad_of_family (s := 12) (R := famF) (by norm_num) (fun k n h => (famF_step k n h).1)
    (fun k n h => (famF_step k n h).2) (famF_use ρ hρ) famF_ex C N

/-- **Quadratic use of the carry rules A** (the combinatorial part of Proposition 3.7): for every carry rule A there are starting points at least `N`
and orbit segments with all points at least 2 on which the number of uses exceeds any linear function `C (lenT n + 1)` of the length of the starting point. -/
theorem aRule_quad (b d : ℕ) (hb : b < 2) (hd : d ≤ 2) (C N : ℕ) :
    ∃ n, N ≤ n ∧ ∃ m, (∀ i < m, 2 ≤ T^[i] n) ∧ C * (lenT n + 1) < usesOrbit (aRule b d) n m := by
  interval_cases b <;> interval_cases d
  · exact quadZ C N
  · exact quadF _ (by simp [patRules]) C N
  · exact quadF _ (by simp [patRules]) C N
  · exact quadF _ (by simp [patRules]) C N
  · exact quadF _ (by simp [patRules]) C N
  · exact quadO C N

end Collatz.Arctic.ARule
