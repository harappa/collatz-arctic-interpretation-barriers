/-
Quadratic use of the carry rules $A$ for the system $\mathcal H$ (Lemma 7.3): the family $F_H$ near the cycle
$3/5 \leftrightarrow 4/5$, and `quadH` for all six carry rules. The $H$ version of `ARuleFive.lean` for $T$
(family F).

* On the 2-adic rationals, $H$ has the cycle $3/5 \to 4/5 \to 3/5$ of period 2 (steps $\mathsf b$, $\mathsf a$). From a point with `5n = 3 + 32E` (`E ≥ 2`),
  two steps ($\mathsf b$, $\mathsf a$) give `5 H² n = 3 + 27E` (`H2_five`): the step $\mathsf b$ gives `5 H n = 4 + 36E`, and the step $\mathsf a$ gives `3 + 27E`.
* **Family $F_H$** (`famFH`): `5n = 3 + 8·2^(20k)·(5w + 4)`. In 8 steps ($\mathsf{babababa}$) a point of stage `k+1` moves to stage `k`
  (`2^20 E' ↦ 27^4 E'`; since `27^4 ≡ 1 (mod 5)`, the form `5w + 4` is preserved, with `w ↦ 531441 w + 425152`).
* **Number of uses**: for a point of stage `k+1`, the number `y₂ = 3m + 2` (`m = (n-7)/8`) of the second sweep of the step $\mathsf b$
  satisfies `5y₂ + 2 = 16^(5k+5)·(5(3w+2) + 2)` (`y₂ ≡ -2/5`), so its low digits are `5k+5` copies of the period `0110`. The initial
  carry is 2; as in the first period of the family F of $T$ (`ARuleFive.famF_use`), the carry becomes 1 in the first period,
  and each later period uses `aRule 0 1`, `aRule 1 0`, `aRule 1 1`, `aRule 0 2` once each (`ARuleCarry.tailBitsLSB_pat`,
  `count_sweep_pat`).
* The remaining two carry rules are covered by the families $Z_H$ (`aRule 0 0`) and $O_H$ (`aRule 1 2`) (`ARule.lean`).
-/
import CollatzProof.Arctic.HTPDB.ARule

namespace Collatz.Arctic.HTPDB

open Collatz.Arctic HModel

namespace ARuleH

/-- Two steps ($\mathsf b$, $\mathsf a$) from a point with `5n = 3 + 32E`: `5 H² n = 3 + 27E`, and the intermediate points lie in the domain. -/
lemma H2_five (n E : ℕ) (hE : 2 ≤ E) (h : 5 * n = 3 + 32 * E) :
    5 * Hmap^[2] n = 3 + 27 * E ∧ ∀ i < 2, HDom (Hmap^[i] n) := by
  have hn : n % 8 = 7 := by omega
  have e1 : 5 * Hmap n = 4 + 36 * E := by rw [u6_Hmap_B hn]; omega
  have hn1 : Hmap n % 4 = 0 := by omega
  have e2 : 5 * Hmap (Hmap n) = 3 + 27 * E := by rw [u6_Hmap_A hn1]; omega
  refine ⟨e2, ?_⟩
  intro i hi
  interval_cases i
  · show HDom n
    exact ⟨by omega, Or.inr hn⟩
  · show HDom (Hmap n)
    exact ⟨by omega, Or.inl hn1⟩

/-- Stage `k` of the family $F_H$: `5n = 3 + 8·2^(20k)·(5w + 4)`. -/
def famFH (k n : ℕ) : Prop := ∃ w, 5 * n = 3 + 8 * (1048576 ^ k * (5 * w + 4))

/-- Splits `H^[8] x` into four blocks of 2 steps (the equalities are chained by explicit terms; see the remark at `Gen.Quad.orbit_appendG'`). -/
lemma iter_8 (x : ℕ) : Hmap^[8] x = Hmap^[2] (Hmap^[2] (Hmap^[2] (Hmap^[2] x))) :=
  (Function.iterate_add_apply Hmap 6 2 x).trans ((Function.iterate_add_apply Hmap 4 2 (Hmap^[2] x)).trans
    (Function.iterate_add_apply Hmap 2 2 (Hmap^[2] (Hmap^[2] x))))

lemma famFH_step (k n : ℕ) (h : famFH (k + 1) n) :
    famFH k (Hmap^[8] n) ∧ ∀ i < 8, HDom (Hmap^[i] n) := by
  obtain ⟨w, hn⟩ := h
  have hP1 : 1 ≤ 1048576 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have h1 : 1048576 ^ (k + 1) * (5 * w + 4) = 1048576 * (1048576 ^ k * (5 * w + 4)) := by
    rw [pow_succ]; ring
  rw [h1] at hn
  generalize hE0 : 1048576 ^ k * (5 * w + 4) = E0 at hn
  have hE0pos : 4 ≤ E0 := by rw [← hE0]; nlinarith
  -- `omega` with large coefficients is slow (it times out), so we use `linarith`. Also, `omega` compares atoms by `isDefEq`, so
  -- we do not call it while hypotheses with different iterates `Hmap^[2] …` are in the context
  have p1 : 2 ≤ 262144 * E0 := by linarith
  have p2 : 2 ≤ 221184 * E0 := by linarith
  have p3 : 2 ≤ 186624 * E0 := by linarith
  have p4 : 2 ≤ 157464 * E0 := by linarith
  obtain ⟨a1, o1⟩ := H2_five n (262144 * E0) p1 (by rw [hn]; ring)
  obtain ⟨a2, o2⟩ := H2_five (Hmap^[2] n) (221184 * E0) p2 (by rw [a1]; ring)
  obtain ⟨a3, o3⟩ := H2_five (Hmap^[2] (Hmap^[2] n)) (186624 * E0) p3 (by rw [a2]; ring)
  obtain ⟨a4, o4⟩ := H2_five (Hmap^[2] (Hmap^[2] (Hmap^[2] n))) (157464 * E0) p4 (by rw [a3]; ring)
  have e4 : Hmap^[2 + 2] n = Hmap^[2] (Hmap^[2] n) := Function.iterate_add_apply Hmap 2 2 n
  have e6 : Hmap^[2 + 2 + 2] n = Hmap^[2] (Hmap^[2] (Hmap^[2] n)) :=
    (Function.iterate_add_apply Hmap 4 2 n).trans (Function.iterate_add_apply Hmap 2 2 (Hmap^[2] n))
  refine ⟨⟨531441 * w + 425152, ?_⟩, ?_⟩
  · have : 1048576 ^ k * (5 * (531441 * w + 425152) + 4) = 531441 * E0 := by rw [← hE0]; ring
    rw [this, iter_8, a4]; ring
  · exact Gen.Quad.orbit_appendG' (Gen.Quad.orbit_appendG' (Gen.Quad.orbit_appendG' o1 rfl o2) e4 o3)
      e6 o4

/-- A point of stage `k+1` uses each rule of `patRules` at least `k` times (in the second sweep of the step $\mathsf b$). -/
lemma famFH_use (ρ : Rule) (hρ : ρ ∈ ARule.patRules) (k n : ℕ) (h : famFH (k + 1) n) :
    k ≤ (canDerivH n).count ρ := by
  obtain ⟨w, hn⟩ := h
  have hρ' : ∃ b d, ρ = aRule b d := by
    simp only [ARule.patRules, List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
  obtain ⟨b, d, rfl⟩ := hρ'
  have hP16 : 1048576 ^ (k + 1) = 16 ^ (5 * k + 5) := by
    rw [show 5 * k + 5 = 5 * (k + 1) by ring, pow_mul]; norm_num
  have hP1 : 1 ≤ 1048576 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
  -- Calling `omega` while hypotheses with powers are in the context makes the kernel check of the proof term very slow (we hide
  -- the powers with `generalize` rather than `set`, and clear the hypotheses on powers before `omega`)
  generalize hQ : 1048576 ^ (k + 1) * (5 * w + 4) = Q at hn
  have hQ4 : 4 ≤ Q := by rw [← hQ]; nlinarith
  have hn7 : n % 8 = 7 := by clear hQ hP16 hP1; omega
  -- The number of the second sweep, `y₂ = 3m + 2`, satisfies `5 y₂ + 2 = 3Q = 16^(5k+5) (5(3w+2) + 2)`
  have hy : 5 * (3 * ((n - 7) / 8) + 2) + 2 = 16 ^ (5 * k + 5) * (5 * (3 * w + 2) + 2) := by
    rw [← hP16]
    have : 1048576 ^ (k + 1) * (5 * (3 * w + 2) + 2) = 3 * Q := by rw [← hQ]; ring
    rw [this]
    clear hQ hP16 hP1 this
    omega
  rw [count_aRule_B _ _ _ hn7, ARule.tailBitsLSB_pat _ _ _ (by omega) hy,
    show 5 * k + 5 = (5 * k + 4) + 1 by ring]
  -- The first period starts with carry 2: after `aRule 0 2`, `aRule 1 1`, `aRule 1 2`, `aRule 0 2` the carry is 1
  have : sweepRules (ARule.pat (5 * k + 4 + 1) ++ tailBitsLSB (3 * w + 2)) 2 =
      aRule 0 2 :: aRule 1 1 :: aRule 1 2 :: aRule 0 2 ::
        sweepRules (ARule.pat (5 * k + 4) ++ tailBitsLSB (3 * w + 2)) 1 := rfl
  rw [this]
  have := ARule.count_sweep_pat (aRule b d) hρ (5 * k + 4) (tailBitsLSB (3 * w + 2))
  have h1 := ARule.count_le_cons (aRule b d) (aRule 0 2)
    (sweepRules (ARule.pat (5 * k + 4) ++ tailBitsLSB (3 * w + 2)) 1)
  have h2 := ARule.count_le_cons (aRule b d) (aRule 1 2) (aRule 0 2 ::
    sweepRules (ARule.pat (5 * k + 4) ++ tailBitsLSB (3 * w + 2)) 1)
  have h3 := ARule.count_le_cons (aRule b d) (aRule 1 1) (aRule 1 2 :: aRule 0 2 ::
    sweepRules (ARule.pat (5 * k + 4) ++ tailBitsLSB (3 * w + 2)) 1)
  have h4 := ARule.count_le_cons (aRule b d) (aRule 0 2) (aRule 1 1 :: aRule 1 2 :: aRule 0 2 ::
    sweepRules (ARule.pat (5 * k + 4) ++ tailBitsLSB (3 * w + 2)) 1)
  omega

lemma famFH_ex (k : ℕ) : ∃ n, k ≤ n ∧ famFH k n ∧ lenT n ≤ 20 * k + 20 := by
  have hP5 : 1048576 ^ k % 5 = 1 := by rw [Nat.pow_mod]; norm_num
  have hPk : k < 1048576 ^ k := Nat.lt_pow_self (by norm_num)
  have h2 : 2 ^ (20 * k + 2 + 1) = 8 * 1048576 ^ k := by
    rw [show 20 * k + 2 + 1 = 20 * k + 3 by ring, pow_add, pow_mul]; norm_num; ring
  have hlen := ARule.lenT_le_of_lt (n := (3 + 32 * 1048576 ^ k) / 5) (L := 20 * k + 2)
    (by rw [h2]; generalize 1048576 ^ k = P at hP5 hPk ⊢; omega)
  -- Hide the powers with `generalize` before `omega` (see the remark in `famFH_use`)
  refine ⟨(3 + 32 * 1048576 ^ k) / 5, ?_, ⟨0, ?_⟩, by omega⟩
  · generalize 1048576 ^ k = P at hP5 hPk ⊢; omega
  · generalize 1048576 ^ k = P at hP5 hPk ⊢; omega

/-- Quadratic use of the four carry rules of `patRules` from the family $F_H$. -/
theorem quadFH (ρ : Rule) (hρ : ρ ∈ ARule.patRules) : Gen.QuadR Hmap HDom canDerivH ρ :=
  Gen.Quad.quad_of_familyG (s := 8) (a := 20) (b := 20) (R := famFH) (by norm_num)
    (fun k n h => (famFH_step k n h).1) (fun k n h => (famFH_step k n h).2) (famFH_use ρ hρ) famFH_ex

end ARuleH

open ARuleH

/-- **Quadratic use of the carry rules** ($\mathcal H$; the $H$ version of the combinatorial part of Proposition 3.7): for each of the six carry rules there are,
with starting points at least `N`, orbit segments of `H` with all points in `HDom` on which the number of uses exceeds any given linear function of the length of the starting point.
Families $Z_H$ (`aRule 0 0`), $O_H$ (`aRule 1 2`), $F_H$ (the other four). -/
theorem quadH (b d : ℕ) (hb : b < 2) (hd : d ≤ 2) : Gen.QuadR Hmap HDom canDerivH (aRule b d) := by
  interval_cases b <;> interval_cases d
  · exact quadZH
  · exact quadFH _ (by simp [ARule.patRules])
  · exact quadFH _ (by simp [ARule.patRules])
  · exact quadFH _ (by simp [ARule.patRules])
  · exact quadFH _ (by simp [ARule.patRules])
  · exact quadOH

/-- **Output on the carry rules** (the 6 carry rules): the frozen `SpecQuadH`. -/
theorem specQuadH : SpecQuadH := quadH

end Collatz.Arctic.HTPDB
