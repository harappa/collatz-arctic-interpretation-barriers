/-
# 𝒯: the lift `Ñ` and `Q'`, and the persistent class `\mathcal P_T` (Lemma 10.6 of the paper)

The lift (indices `Q × ℤ/M`, exits restricted to a set `Pc` of residue classes) and the persistent class of 𝒯,
`\mathcal P_T = {3 ∤ n}` (`M = 3`, `Pc = {1, 2}`).

* **Binary values** (§1): the Horner value `valW r ω` (starting from `r`, reading from the most significant digit). `valW 1 (binWord n) = n` (`n ≥ 1`,
  `valW_binWord`): the value of the word `1 ω` read from the leading 1.
* **The lift** (§2): `(Ñ_b)_{(k,r),(k',r')} := (N_b)_{kk'} [r' ≡ 2r + b]`, `ũ_{(k,r)} := u_k [r ≡ 1]`,
  `ṽ_{(k,r)} := v_k [r ∈ Pc]` (`lift`, with start residue 1). The form of products of words (`DxN_lift`:
  `(Ñ_ω)_{(k,r),(k',r')} = (N_ω)_{kk'} [r' ≡ 2^{|ω|} r + val(ω)]`) and **the identity of values** (Lemma 10.6 (ii), `aval_lift`:
  `ũ^T Ñ_ω ṽ = V(ω) [val(1ω) mod M ∈ Pc]`). The lift is not an interpretation (there are no inequalities of rules).
* **𝒯** (§3): `liftT A := lift A 3 {1, 2}`. `aval (liftT A) (binWord n) = aval A (binWord n) [3 ∤ n]` (`n ≥ 1`,
  `aval_liftT`). `\tilde V` does not increase along steps of `T` (`3 ∤ n`, `n ≥ 2`, `gavalT_T_le`). The multiples of 3 form a transient class
  (`three_dvd_of_three_dvd_T`, `not_three_dvd_T_of_odd`, `not_three_dvd_iterate`).
  **`Q'`** is `relSet (liftT A)`, and the components of `Q'` are `IsComp (liftT A)` (`Compartment.lean`).
  For natural-number matrix interpretations, `liftNat I := liftT (natAuto I)` (`aval_liftNat`).
-/
import CollatzProof.Arctic.Nat.Compartment

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Matrix

set_option linter.unusedSectionVars false

/-! ## §1 Binary values -/

/-- The Horner value: starting from `r`, read the word `ω` from the most significant digit (`valW r (b :: ω) = valW (2r + b) ω`). -/
def valW : ℕ → List (Fin 2) → ℕ
  | r, [] => r
  | r, b :: w => valW (2 * r + b) w

theorem valW_eq (r : ℕ) (w : List (Fin 2)) : valW r w = r * 2 ^ w.length + valW 0 w := by
  induction w generalizing r with
  | nil => simp [valW]
  | cons b w ih =>
    simp only [valW, List.length_cons]
    rw [ih, ih (0 * 2 + b)]
    ring

theorem valW_append_single (r : ℕ) (w : List (Fin 2)) (b : Fin 2) :
    valW r (w ++ [b]) = 2 * valW r w + b := by
  induction w generalizing r with
  | nil => simp [valW]
  | cons c w ih => simp only [List.cons_append, valW]; exact ih _

/-- The value of a list of binary digits (`l` from the least significant digit). -/
theorem valW_reverse_map (r : ℕ) (l : List ℕ) (hl : ∀ d ∈ l, d < 2) :
    valW r (l.reverse.map (fun b => if b = 0 then (0 : Fin 2) else 1)) = r * 2 ^ l.length + Nat.ofDigits 2 l := by
  induction l with
  | nil => simp [valW]
  | cons d l ih =>
    have hd : d < 2 := hl d List.mem_cons_self
    have ih' := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
    rw [List.reverse_cons, List.map_append, List.map_singleton, valW_append_single, ih',
      Nat.ofDigits_cons, List.length_cons, pow_succ]
    have hb : ((if d = 0 then (0 : Fin 2) else 1 : Fin 2) : ℕ) = d := by
      rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl <;> rfl
    rw [hb]; ring

/-- **`valW 1 (binWord n) = n`** (`n ≥ 1`): `binWord n` consists of the binary digits without the leading 1. -/
theorem valW_binWord (n : ℕ) (hn : 1 ≤ n) : valW 1 (binWord n) = n := by
  set L := Nat.digits 2 n
  have hL : L ≠ [] := Nat.digits_ne_nil_iff_ne_zero.2 (by omega)
  have hlast : L.getLast hL = 1 := by
    have h1 : L.getLast hL ≠ 0 := Nat.getLast_digit_ne_zero 2 (m := n) (by omega)
    have h2 : L.getLast hL < 2 := Nat.digits_lt_base (by norm_num) (List.getLast_mem hL)
    omega
  have hsplit : L = L.dropLast ++ [1] := by
    conv_lhs => rw [← List.dropLast_append_getLast hL]
    rw [hlast]
  have hlt : ∀ d ∈ L.dropLast, d < 2 := fun d hd =>
    Nat.digits_lt_base (by norm_num) (List.dropLast_subset _ hd)
  have hbw : binWord n = (L.dropLast.reverse).map (fun b => if b = 0 then (0 : Fin 2) else 1) := by
    unfold binWord
    rw [show (Nat.digits 2 n) = L from rfl]
    conv_lhs => rw [hsplit]
    simp
  rw [hbw, valW_reverse_map 1 _ hlt, one_mul]
  have := Nat.ofDigits_digits 2 n
  rw [show Nat.digits 2 n = L from rfl, hsplit, Nat.ofDigits_append, Nat.ofDigits_singleton] at this
  omega

/-! ## §2 The lift -/

section Lift

variable {Q : Type*} [Fintype Q] [DecidableEq Q] {M : ℕ} [NeZero M]

/-- The digit matrices of the lift `(Ñ_b)_{(k,r),(k',r')} := (N_b)_{kk'} [r' ≡ 2r + b]` (congruence modulo `M`). -/
def liftB (A : ValAuto Q) (M : ℕ) (b : Fin 2) : Matrix (Q × ZMod M) (Q × ZMod M) ℕ :=
  fun p p' => A.B b p.1 p'.1 * if p'.2 = 2 * p.2 + ((b : ℕ) : ZMod M) then 1 else 0

/-- **The lift** `Ñ`: indices `Q × ℤ/M`, start at residue `1` (after reading the leading 1), exits at the classes with residue in `Pc`. -/
def lift (A : ValAuto Q) (M : ℕ) (Pc : Finset (ZMod M)) : ValAuto (Q × ZMod M) where
  B := liftB A M
  u p := A.u p.1 * if p.2 = 1 then 1 else 0
  v p := A.v p.1 * if p.2 ∈ Pc then 1 else 0

/-- Products of words of the lift: `(Ñ_ω)_{(k,r),(k',r')} = (N_ω)_{kk'} [r' ≡ 2^{|ω|} r + val(ω)]`. -/
theorem DxN_lift (A : ValAuto Q) (ω : List (Fin 2)) (k k' : Q) (r r' : ZMod M) :
    Rigid.DxN (liftB A M) ω (k, r) (k', r') =
      Rigid.DxN A.B ω k k' * if r' = 2 ^ ω.length * r + ((valW 0 ω : ℕ) : ZMod M) then 1 else 0 := by
  induction ω generalizing k r with
  | nil =>
    simp only [DxN_nil', Matrix.one_apply, Prod.mk.injEq, List.length_nil, pow_zero, one_mul, valW,
      Nat.cast_zero, add_zero]
    by_cases hk : k = k' <;> by_cases hr : r = r' <;> simp [hk, hr, Ne.symm]
  | cons b ω ih =>
    rw [DxN_cons', Matrix.mul_apply, Fintype.sum_prod_type, DxN_cons', Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [liftB, ih]
    have hval : ((valW 0 (b :: ω) : ℕ) : ZMod M) = ((b : ℕ) : ZMod M) * 2 ^ ω.length + ((valW 0 ω : ℕ) : ZMod M) := by
      simp only [valW]
      rw [valW_eq]; push_cast; ring
    rw [Finset.sum_eq_single (2 * r + ((b : ℕ) : ZMod M))]
    · simp only [ite_true, mul_one, List.length_cons, hval]
      have : (2 : ZMod M) ^ ω.length * (2 * r + ((b : ℕ) : ZMod M)) + ((valW 0 ω : ℕ) : ZMod M) =
          2 ^ (ω.length + 1) * r + (((b : ℕ) : ZMod M) * 2 ^ ω.length + ((valW 0 ω : ℕ) : ZMod M)) := by ring
      rw [this]; ring
    · intro s _ hs
      simp [hs]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- **The identity of values** (Lemma 10.6 (ii)): `ũ^T Ñ_ω ṽ = (u^T N_ω v) [val(1ω) mod M ∈ Pc]`. -/
theorem aval_lift (A : ValAuto Q) (Pc : Finset (ZMod M)) (ω : List (Fin 2)) :
    aval (lift A M Pc) ω = aval A ω * if (((valW 1 ω : ℕ) : ZMod M) ∈ Pc) then 1 else 0 := by
  rw [aval_eq_sum, aval_eq_sum, Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single (1 : ZMod M)]
  · rw [Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [Finset.sum_eq_single (2 ^ ω.length * (1 : ZMod M) + ((valW 0 ω : ℕ) : ZMod M))]
    · have hv : (((valW 1 ω : ℕ) : ZMod M)) = 2 ^ ω.length * 1 + ((valW 0 ω : ℕ) : ZMod M) := by
        rw [valW_eq]; push_cast; ring
      simp only [lift, DxN_lift, ite_true, mul_one, hv]
      split_ifs <;> ring
    · intro s _ hs
      simp only [lift, DxN_lift, hs, ite_false, mul_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro r _ hr
    refine Finset.sum_eq_zero fun p _ => ?_
    simp [lift, hr]
  · intro h; exact absurd (Finset.mem_univ _) h

end Lift

/-! ## §3 𝒯: `\mathcal P_T = {3 ∤ n}` -/

/-- The residues `Π = {1, 2} ⊆ ℤ/3` of the persistent class of 𝒯. -/
def PcT : Finset (ZMod 3) := {1, 2}

theorem mem_PcT (x : ZMod 3) : x ∈ PcT ↔ x ≠ 0 := by
  revert x; decide

section ST

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The lift for 𝒯 (the lift modulo 3 of Lemma 10.6 of the paper). -/
def liftT (A : ValAuto Q) : ValAuto (Q × ZMod 3) := lift A 3 PcT

/-- **`\tilde V(n) = V(n) [3 ∤ n]`** (`n ≥ 1`). -/
theorem aval_liftT (A : ValAuto Q) (n : ℕ) (hn : 1 ≤ n) :
    aval (liftT A) (binWord n) = aval A (binWord n) * if 3 ∣ n then 0 else 1 := by
  rw [liftT, aval_lift, valW_binWord n hn]
  simp only [mem_PcT]
  by_cases h : 3 ∣ n
  · have : ((n : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff n 3).2 h
    simp [h, this]
  · have : ((n : ℕ) : ZMod 3) ≠ 0 := fun h' => h ((ZMod.natCast_eq_zero_iff n 3).1 h')
    simp [h, this]

/-- **`Q'`**: the relevant indices of the lift (those reachable from a start index `(k, 1)` (`u_k > 0`) and from which an exit
`(k, r)` (`v_k > 0`, `r ≠ 0`) can be reached). The restriction `\tilde u'`, `\tilde B'`, `\tilde v'` to `Q'` is `restrictRel (liftT A)`,
and it does not change the values (`aval_restrictRel`). The components of `Q'` are `IsComp (liftT A)`. -/
noncomputable def QPrime (A : ValAuto Q) : Finset (Q × ZMod 3) := relSet (liftT A)

theorem mem_QPrime (A : ValAuto Q) (p : Q × ZMod 3) : p ∈ QPrime A ↔ Rel (liftT A) p := mem_relSet _

/-- The predicate `n ∈ \mathcal P` of the persistent class (a union of residue classes, condition (P1) of an earlier written argument; (P2) is a property of the point family, treated in Section 12). -/
def InP (M : ℕ) (Pc : Finset (ZMod M)) (n : ℕ) : Prop := ((n : ℕ) : ZMod M) ∈ Pc

theorem inP_T_iff (n : ℕ) : InP 3 PcT n ↔ ¬ 3 ∣ n := by
  unfold InP
  rw [mem_PcT, Ne, ZMod.natCast_eq_zero_iff]

/-- For `n` not divisible by 3, `\tilde V(n) = V(n)`. -/
theorem aval_liftT_of_not_dvd (A : ValAuto Q) {n : ℕ} (hn : 1 ≤ n) (h : ¬ 3 ∣ n) :
    aval (liftT A) (binWord n) = aval A (binWord n) := by
  rw [aval_liftT A n hn]; simp [h]

/-- If `3 ∣ T n`, then `3 ∣ n` (the multiples of 3 form a transient class). -/
theorem three_dvd_of_three_dvd_T {n : ℕ} (h : 3 ∣ T n) : 3 ∣ n := by
  unfold T at h
  split_ifs at h with hn <;> omega

/-- The image of an odd step is not divisible by 3. -/
theorem not_three_dvd_T_of_odd {n : ℕ} (hn : n % 2 = 1) : ¬ 3 ∣ T n := by
  unfold T
  split_ifs <;> omega

/-- The orbit of a number not divisible by 3 does not pass through multiples of 3. -/
theorem not_three_dvd_iterate {n : ℕ} (h : ¬ 3 ∣ n) : ∀ k, ¬ 3 ∣ T^[k] n := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact fun h' => ih (three_dvd_of_three_dvd_T h')

theorem one_le_T {n : ℕ} (hn : 2 ≤ n) : 1 ≤ T n := by
  unfold T; split_ifs <;> omega

/-- For general families, `\tilde V` does not increase along steps of `T` at `n ≥ 2` not divisible by 3 (the version of Lemma 10.2 (iii) for the lift). -/
theorem gavalT_T_le {N : Letter → Matrix Q Q ℕ} (hweak : ∀ ρ ∈ rulesST, GWeak N ρ) (a z : Q) {n : ℕ}
    (hn : 2 ≤ n) (h3 : ¬ 3 ∣ n) :
    aval (liftT (genAuto N a z)) (binWord (T n)) ≤ aval (liftT (genAuto N a z)) (binWord n) := by
  have h3' : ¬ 3 ∣ T n := fun h' => h3 (three_dvd_of_three_dvd_T h')
  rw [aval_liftT_of_not_dvd _ (one_le_T hn) h3', aval_liftT_of_not_dvd _ (by omega) h3,
    ← nw_can_eq_aval, ← nw_can_eq_aval]
  exact gnw_can_T_le hweak n hn a z

/-- The lift for natural-number matrix interpretations (indices `(k, r)`, where `k` ranges over indices including the homogeneous index). -/
def liftNat {d : ℕ} [NeZero d] (I : Letter → NAff d) : ValAuto (Option (Fin d) × ZMod 3) := liftT (natAuto I)

theorem aval_liftNat {d : ℕ} [NeZero d] (I : Letter → NAff d) (n : ℕ) (hn : 1 ≤ n) :
    aval (liftNat I) (binWord n) = PhiN I (can n) * if 3 ∣ n then 0 else 1 := by
  rw [liftNat, aval_liftT _ n hn, ← phiN_can_eq_aval]

end ST

end Collatz.Arctic.NatQ5
