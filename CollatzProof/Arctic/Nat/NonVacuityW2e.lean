/-
# Natural-number matrix interpretations ($\mathcal T$): non-vacuity checks for Theorem 10.8 and Corollary 10.9 of the paper (outside the closure; three examples requested by an internal review)

The conclusion `H2Prod` of the main theorems of `H2Main.lean` (`zeroOne_of_T_mono`, `h2Prod_of_autoMono`, `h2Core`) is not trivial.

* §1 **If the products of the base automaton are 0/1, then `H2Prod`** (`h2Prod_of_base_zeroOne`, a general lemma).
* §2 **A constant plus a lane modulo 3**, `laneAuto c := addConst (lift two 3 {c})`: the value is `V(n) = 1 + 2^{ℓ'(n)} [n ≡ c (mod 3)]`
  (`aval_laneAuto`). A lane of permutations with weight 2 (of the type of Proposition 9.5 of the paper) with an added constant index of weight 1.
* §3 **Exit residue 0**: `AutoMono ∧ ZeroFree ∧ H2Prod` (`lane0_props`), and the base automaton has a component that is not 0/1
  (`lane0_base_not_zeroOne`). `H2Prod` follows both from the main theorem (`h2Prod_of_autoMono`) and from a direct proof that does not use it
  (`h2Prod_lane0_direct`: in the lift no index of the lane is relevant).
* §4 **Exit residue 2**: `¬ AutoMono ∧ ¬ H2Prod` (`lane2_props`; at `n = 3`, `V(T 3) = V(5) = 5 > 1 = V(3)`, and the lift has
  a component of weight 2). This agrees with the contrapositive of `h2Core`.

Computations use `decide +kernel` and `simp` (`native_decide` is not used).
-/
import CollatzProof.Arctic.Nat.H2Main

namespace Collatz.Arctic.NatQ5.W2e.NonVacuity

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W2a Collatz.Arctic.NatQ5.W2e Matrix

set_option linter.unusedSectionVars false

/-! ## §1 If the products of the base automaton are 0/1, then `H2Prod` -/

section Base

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- **If the products of the base automaton are 0/1, then (H2^prod)**: an entry of a product of the lift is the entry of the product of the base automaton times the indicator of the residues (`DxN_lift`). -/
theorem h2Prod_of_base_zeroOne (A : ValAuto Q) (h : ∀ w i j, Rigid.DxN A.B w i j ≤ 1) : H2Prod A := by
  rintro C ⟨⟨q, -, rfl⟩, -⟩ w x y
  rw [DC_apply]
  change Rigid.DxN (liftB A 3) w (x.1.1, x.1.2) (y.1.1, y.1.2) ≤ 1
  rw [DxN_lift]
  split_ifs
  · rw [mul_one]; exact h w _ _
  · simp

end Base

/-! ## §2 A constant plus a lane modulo 3 -/

section AddConst

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The automaton with an added constant index `none` (a self-loop of weight 1, entries 1 in `û` and `v̂`; the value is `V_A + 1`). -/
def addConst (A : ValAuto Q) : ValAuto (Option Q) where
  B b p q := match p, q with
    | some i, some j => A.B b i j
    | none, none => 1
    | _, _ => 0
  u p := match p with
    | some i => A.u i
    | none => 1
  v p := match p with
    | some i => A.v i
    | none => 1

@[simp] theorem addConst_B_ss (A : ValAuto Q) (b : Fin 2) (i j : Q) : (addConst A).B b (some i) (some j) = A.B b i j := rfl
@[simp] theorem addConst_B_sn (A : ValAuto Q) (b : Fin 2) (i : Q) : (addConst A).B b (some i) none = 0 := rfl
@[simp] theorem addConst_B_ns (A : ValAuto Q) (b : Fin 2) (j : Q) : (addConst A).B b none (some j) = 0 := rfl
@[simp] theorem addConst_B_nn (A : ValAuto Q) (b : Fin 2) : (addConst A).B b none none = 1 := rfl
@[simp] theorem addConst_u_s (A : ValAuto Q) (i : Q) : (addConst A).u (some i) = A.u i := rfl
@[simp] theorem addConst_u_n (A : ValAuto Q) : (addConst A).u none = 1 := rfl
@[simp] theorem addConst_v_s (A : ValAuto Q) (i : Q) : (addConst A).v (some i) = A.v i := rfl
@[simp] theorem addConst_v_n (A : ValAuto Q) : (addConst A).v none = 1 := rfl

theorem DxN_addConst_ss (A : ValAuto Q) (w : List (Fin 2)) (i j : Q) :
    Rigid.DxN (addConst A).B w (some i) (some j) = Rigid.DxN A.B w i j := by
  induction w generalizing i with
  | nil => simp [Matrix.one_apply]
  | cons b w ih =>
    rw [DxN_cons', Matrix.mul_apply, Fintype.sum_option, DxN_cons', Matrix.mul_apply]
    simp only [addConst_B_sn, zero_mul, zero_add, addConst_B_ss, ih]

theorem DxN_addConst_ns (A : ValAuto Q) (w : List (Fin 2)) (j : Q) :
    Rigid.DxN (addConst A).B w none (some j) = 0 := by
  induction w with
  | nil => simp
  | cons b w ih =>
    rw [DxN_cons', Matrix.mul_apply, Fintype.sum_option]
    simp only [addConst_B_nn, one_mul, ih, addConst_B_ns, zero_mul, Finset.sum_const_zero, add_zero]

theorem DxN_addConst_sn (A : ValAuto Q) (w : List (Fin 2)) (i : Q) :
    Rigid.DxN (addConst A).B w (some i) none = 0 := by
  induction w generalizing i with
  | nil => simp
  | cons b w ih =>
    rw [DxN_cons', Matrix.mul_apply, Fintype.sum_option]
    simp only [addConst_B_sn, zero_mul, ih, mul_zero, Finset.sum_const_zero, add_zero]

theorem DxN_addConst_nn (A : ValAuto Q) (w : List (Fin 2)) : Rigid.DxN (addConst A).B w none none = 1 := by
  induction w with
  | nil => simp
  | cons b w ih =>
    rw [DxN_cons', Matrix.mul_apply, Fintype.sum_option]
    simp only [addConst_B_nn, one_mul, ih, addConst_B_ns, zero_mul, Finset.sum_const_zero, add_zero]

theorem aval_addConst (A : ValAuto Q) (ω : List (Fin 2)) : aval (addConst A) ω = aval A ω + 1 := by
  rw [aval_eq_sum, aval_eq_sum, Fintype.sum_option]
  simp only [Fintype.sum_option, addConst_u_n, addConst_u_s, addConst_v_n, addConst_v_s, DxN_addConst_ss,
    DxN_addConst_ns, DxN_addConst_sn, DxN_addConst_nn, mul_one, one_mul, mul_zero, zero_mul,
    Finset.sum_const_zero, zero_add, add_zero]
  ring

theorem addConst_g2 (A : ValAuto Q) : AutoG2 (addConst A) := ⟨none, fun b => (addConst_B_nn A b).ge⟩

end AddConst

/-- The one-state automaton of weight 2 (`B_b = (2)`, `û = v̂ = (1)`, value `2^{|ω|}`). -/
def two : ValAuto Unit where
  B _ := fun _ _ => 2
  u _ := 1
  v _ := 1

theorem DxN_two (w : List (Fin 2)) : Rigid.DxN two.B w () () = 2 ^ w.length := by
  induction w with
  | nil => simp
  | cons b w ih =>
    rw [DxN_cons', Matrix.mul_apply, Fintype.sum_unique]
    change two.B b () () * Rigid.DxN two.B w () () = 2 ^ (w.length + 1)
    rw [ih, pow_succ]
    change 2 * 2 ^ w.length = 2 ^ w.length * 2
    ring

theorem aval_two (ω : List (Fin 2)) : aval two ω = 2 ^ ω.length := by
  rw [aval_eq_sum, Fintype.sum_unique, Fintype.sum_unique]
  change two.u () * Rigid.DxN two.B ω () () * two.v () = _
  rw [DxN_two]
  change 1 * 2 ^ ω.length * 1 = _
  ring

/-- **A constant plus a lane modulo 3** (exit residue `c`). -/
def laneAuto (c : ZMod 3) : ValAuto (Option (Unit × ZMod 3)) := addConst (lift two 3 {c})

/-- `V(ω) = 2^{|ω|} [val(1ω) ≡ c] + 1`. -/
theorem aval_laneAuto (c : ZMod 3) (ω : List (Fin 2)) :
    aval (laneAuto c) ω = 2 ^ ω.length * (if ((valW 1 ω : ℕ) : ZMod 3) = c then 1 else 0) + 1 := by
  rw [laneAuto, aval_addConst, aval_lift, aval_two]
  simp

/-- `V(n) = 2^{ℓ'(n)} [n ≡ c (mod 3)] + 1` (`n ≥ 1`). -/
theorem aval_laneAuto_binWord (c : ZMod 3) {n : ℕ} (hn : 1 ≤ n) :
    aval (laneAuto c) (binWord n) = 2 ^ (binWord n).length * (if ((n : ℕ) : ZMod 3) = c then 1 else 0) + 1 := by
  rw [aval_laneAuto, valW_binWord n hn]

theorem zeroFree_lane (c : ZMod 3) : ZeroFree (laneAuto c) := zeroFree_of_g2 (addConst_g2 _)

/-- Products on the indices of the lane: `(B_w)_{(ρ),(ρ')} = 2^{|w|} [ρ' = 2^{|w|} ρ + val(w)]`. -/
theorem DxN_lane_ss (c : ZMod 3) (w : List (Fin 2)) (ρ ρ' : ZMod 3) :
    Rigid.DxN (laneAuto c).B w (some ((), ρ)) (some ((), ρ')) =
      2 ^ w.length * if ρ' = 2 ^ w.length * ρ + ((valW 0 w : ℕ) : ZMod 3) then 1 else 0 := by
  rw [laneAuto, DxN_addConst_ss]
  change Rigid.DxN (liftB two 3) w ((), ρ) ((), ρ') = _
  rw [DxN_lift, DxN_two]

theorem DxN_lane_ns (c : ZMod 3) (w : List (Fin 2)) (p : Unit × ZMod 3) :
    Rigid.DxN (laneAuto c).B w none (some p) = 0 := DxN_addConst_ns _ w p

theorem DxN_lane_sn (c : ZMod 3) (w : List (Fin 2)) (p : Unit × ZMod 3) :
    Rigid.DxN (laneAuto c).B w (some p) none = 0 := DxN_addConst_sn _ w p

theorem DxN_lane_nn (c : ZMod 3) (w : List (Fin 2)) : Rigid.DxN (laneAuto c).B w none none = 1 :=
  DxN_addConst_nn _ w

/-! ## §3 Exit residue 0: `AutoMono ∧ ZeroFree ∧ H2Prod`, and a component of the base automaton that is not 0/1 -/

/-- The values of the lane with residue 0 do not increase along steps of `T`. The image `T n` is a multiple of 3 only if `n` is an even multiple of 3,
and then `ℓ'(n/2) < ℓ'(n)`. -/
theorem autoMono_lane0 : AutoMono (laneAuto 0) := by
  intro n hn
  have hTn := one_le_T hn
  rw [aval_laneAuto_binWord 0 hTn, aval_laneAuto_binWord 0 (by omega)]
  have hlen : ∀ (h3' : 3 ∣ Collatz.Arctic.T n),
      2 ^ (binWord (Collatz.Arctic.T n)).length ≤ 2 ^ (binWord n).length ∧ 3 ∣ n := by
    intro h3'
    have hn3 : 3 ∣ n := three_dvd_of_three_dvd_T h3'
    have hev : n % 2 = 0 := by
      by_contra hodd
      exact not_three_dvd_T_of_odd (by omega) h3'
    have hT2 : Collatz.Arctic.T n = n / 2 := by unfold Collatz.Arctic.T; simp [hev]
    have hlo := (binWord_length_bounds _ hTn).1
    have hhi := (binWord_length_bounds n (by omega)).2
    refine ⟨?_, hn3⟩
    rw [pow_succ] at hhi
    rw [hT2] at hlo ⊢
    omega
  split_ifs with h3 hn3
  · have := (hlen ((ZMod.natCast_eq_zero_iff _ 3).1 h3)).1
    omega
  · exact absurd ((ZMod.natCast_eq_zero_iff _ 3).2 (hlen ((ZMod.natCast_eq_zero_iff _ 3).1 h3)).2) hn3
  · omega
  · omega

/-- `H2Prod` from the main theorem (`h2Prod_of_autoMono`). -/
theorem h2Prod_lane0 : H2Prod (laneAuto 0) := h2Prod_of_autoMono autoMono_lane0

theorem lane0_props : AutoMono (laneAuto 0) ∧ ZeroFree (laneAuto 0) ∧ H2Prod (laneAuto 0) :=
  ⟨autoMono_lane0, zeroFree_lane 0, h2Prod_lane0⟩

/-- The base indices `q₁ := (lane, residue 1)` and `q₂ := (lane, residue 2)`. -/
abbrev q₁ : Option (Unit × ZMod 3) := some ((), 1)
abbrev q₂ : Option (Unit × ZMod 3) := some ((), 2)

theorem lane_q1_q2 (c : ZMod 3) : Rigid.DxN (laneAuto c).B [0] q₁ q₂ = 2 := by
  rw [DxN_lane_ss]; decide

theorem lane_q2_q1 (c : ZMod 3) : Rigid.DxN (laneAuto c).B [0] q₂ q₁ = 2 := by
  rw [DxN_lane_ss]; decide

theorem q2_mem_scc_base (c : ZMod 3) : q₂ ∈ sccOf (laneAuto c) q₁ :=
  (mem_sccOf _).2 ⟨⟨[0], by rw [lane_q1_q2]; norm_num⟩, ⟨[0], by rw [lane_q2_q1]; norm_num⟩⟩

/-- **The base automaton has a component that is not 0/1** (the lane with residue 0: `q₁` is the start index and reaches the exit `(lane, residue 0)` by the word `1`,
so it is relevant, and `q₁ ⇄ q₂` has weight 2). The conclusion `H2Prod` of the main theorem concerns the lift; it does not hold for the base automaton. -/
theorem lane0_base_not_zeroOne : ∃ C, IsComp (laneAuto 0) C ∧ ¬ ZeroOne (laneAuto 0) C := by
  have hrel : Rel (laneAuto 0) q₁ := by
    refine ⟨⟨q₁, by decide, conn_refl _ _⟩, ⟨some ((), 0), ⟨[1], ?_⟩, by decide⟩⟩
    rw [DxN_lane_ss]; decide
  refine ⟨sccOf (laneAuto 0) q₁, ⟨⟨q₁, hrel, rfl⟩, ⟨q₁, self_mem_sccOf _ _, q₂, q2_mem_scc_base 0, 0, by decide⟩⟩, ?_⟩
  intro h01
  have := h01 [0] ⟨q₁, self_mem_sccOf _ _⟩ ⟨q₂, q2_mem_scc_base 0⟩
  rw [DC_apply, lane_q1_q2] at this
  omega

/-! ### `H2Prod (laneAuto 0)` without the main theorem: in the lift no index of the lane is relevant -/

/-- Products of the lift: `(Ñ_w)_{(k,r),(k',r')} = (B_w)_{kk'} [r' = 2^{|w|} r + val(w)]`. -/
theorem DxN_liftT (A : ValAuto (Option (Unit × ZMod 3))) (w : List (Fin 2)) (k k' : Option (Unit × ZMod 3))
    (r r' : ZMod 3) :
    Rigid.DxN (liftT A).B w (k, r) (k', r') =
      Rigid.DxN A.B w k k' * if r' = 2 ^ w.length * r + ((valW 0 w : ℕ) : ZMod 3) then 1 else 0 :=
  DxN_lift A w k k' r r'

/-- An index `(some (ρ), r)` that can be reached from the start in the lift has `ρ = r`. -/
theorem lane0_reach {ρ r : ZMod 3} (h : Reach (liftT (laneAuto 0)) (some ((), ρ), r)) : ρ = r := by
  obtain ⟨⟨k, r0⟩, hu, w, hw⟩ := h
  rcases k with _ | ⟨⟨⟩, ρ0⟩
  · rw [DxN_liftT, DxN_lane_ns] at hw; simp at hw
  · have hu' : 1 ≤ (if ρ0 = 1 then 1 else 0) * (if r0 = 1 then 1 else 0) := by
      simpa [liftT, lift, laneAuto, two] using hu
    have hρ0 : ρ0 = 1 := by by_contra h; simp [h] at hu'
    have hr0 : r0 = 1 := by by_contra h; simp [h] at hu'
    subst hρ0 hr0
    rw [DxN_liftT, DxN_lane_ss] at hw
    split_ifs at hw with h1 h2 <;> simp_all

/-- In the lift, no exit can be reached from an index `(some (ρ), ρ)` of the lane (an exit has `ρ' = 0` and `r' ≠ 0`, and the residue of the lane and
that of the lift move together). -/
theorem lane0_not_coReach (ρ : ZMod 3) : ¬ CoReach (liftT (laneAuto 0)) (some ((), ρ), ρ) := by
  rintro ⟨⟨k', r'⟩, ⟨w, hw⟩, hv⟩
  rcases k' with _ | ⟨⟨⟩, ρ'⟩
  · rw [DxN_liftT, DxN_lane_sn] at hw; simp at hw
  · have hv' : 1 ≤ (if ρ' = 0 then 1 else 0) * (if r' ∈ PcT then 1 else 0) := by
      simpa [liftT, lift, laneAuto, two] using hv
    have hρ' : ρ' = 0 := by by_contra h; simp [h] at hv'
    have hr' : r' ∈ PcT := by by_contra h; simp [h] at hv'
    rw [DxN_liftT, DxN_lane_ss] at hw
    split_ifs at hw with h1 h2
    · have : r' = 0 := by rw [h2, ← h1, hρ']
      exact (mem_PcT r').1 hr' this
    all_goals simp at hw

/-- **The form without the main theorem**: every component of the lift of the lane with residue 0 consists of constant indices only, and it is 0/1. -/
theorem h2Prod_lane0_direct : H2Prod (laneAuto 0) := by
  rintro C ⟨⟨⟨k, r⟩, hq, rfl⟩, -⟩ w x y
  -- the relevant indices are the constant indices `(none, r)`
  have hk : k = none := by
    rcases k with _ | ⟨⟨⟩, ρ⟩
    · rfl
    · exfalso
      have hρ := lane0_reach hq.1
      subst hρ
      exact lane0_not_coReach _ hq.2
  subst hk
  -- the points of the component are constant indices too (no index of the lane can be reached from a constant index)
  have hnone : ∀ z ∈ sccOf (liftT (laneAuto 0)) (none, r), z.1 = none := by
    rintro ⟨k', r'⟩ hz
    obtain ⟨⟨v, hv⟩, -⟩ := (mem_sccOf _).1 hz
    rcases k' with _ | ⟨⟨⟩, ρ'⟩
    · rfl
    · rw [DxN_liftT, DxN_lane_ns] at hv; simp at hv
  rw [DC_apply]
  obtain ⟨⟨kx, rx⟩, hx⟩ := x
  obtain ⟨⟨ky, ry⟩, hy⟩ := y
  have hkx : kx = none := hnone _ hx
  have hky : ky = none := hnone _ hy
  subst hkx hky
  rw [DxN_liftT, DxN_lane_nn]
  split_ifs <;> simp

/-! ## §4 Exit residue 2: `¬ AutoMono ∧ ¬ H2Prod` -/

theorem lane2_not_autoMono : ¬ AutoMono (laneAuto 2) := by
  intro h
  have h3 := h 3 (by norm_num)
  have hT : Collatz.Arctic.T 3 = 5 := by decide
  rw [hT, aval_laneAuto_binWord 2 (by norm_num), aval_laneAuto_binWord 2 (by norm_num)] at h3
  have e5 : (binWord 5).length = 2 := by decide +kernel
  rw [e5] at h3
  revert h3
  decide

/-- The indices `p₁ := (q₁, 1)`, `p₂ := (q₂, 2)` of the lift. -/
abbrev p₁ : Option (Unit × ZMod 3) × ZMod 3 := (q₁, 1)
abbrev p₂ : Option (Unit × ZMod 3) × ZMod 3 := (q₂, 2)

theorem lift_p1_p2 (c : ZMod 3) : Rigid.DxN (liftT (laneAuto c)).B [0] p₁ p₂ = 2 := by
  rw [DxN_liftT, lane_q1_q2]; decide

theorem lift_p2_p1 (c : ZMod 3) : Rigid.DxN (liftT (laneAuto c)).B [0] p₂ p₁ = 2 := by
  rw [DxN_liftT, lane_q2_q1]; decide

theorem p2_mem_scc (c : ZMod 3) : p₂ ∈ sccOf (liftT (laneAuto c)) p₁ :=
  (mem_sccOf _).2 ⟨⟨[0], by rw [lift_p1_p2]; norm_num⟩, ⟨[0], by rw [lift_p2_p1]; norm_num⟩⟩

/-- The lift of the lane with residue 2 has a component of weight 2 (`p₁` is a start index and `p₂` an exit: `(lane, residue 2)`, and the residue 2 of the lift
is a class of numbers not divisible by 3). -/
theorem lane2_not_h2Prod : ¬ H2Prod (laneAuto 2) := by
  intro h
  have hu : 1 ≤ (liftT (laneAuto 2)).u p₁ := by decide
  have hv : 1 ≤ (liftT (laneAuto 2)).v p₂ := by decide
  have hrel : Rel (liftT (laneAuto 2)) p₁ :=
    ⟨⟨p₁, hu, conn_refl _ _⟩, ⟨p₂, ⟨[0], by rw [lift_p1_p2]; norm_num⟩, hv⟩⟩
  have hedge : HasEdge (liftT (laneAuto 2)) (sccOf (liftT (laneAuto 2)) p₁) :=
    ⟨p₁, self_mem_sccOf _ _, p₂, p2_mem_scc 2, 0, by
      have := lift_p1_p2 2
      rw [show Rigid.DxN (liftT (laneAuto 2)).B [0] p₁ p₂ = (liftT (laneAuto 2)).B 0 p₁ p₂ by
        simp [Rigid.DxN]] at this
      omega⟩
  have h01 := h _ ⟨⟨p₁, hrel, rfl⟩, hedge⟩
  have := h01 [0] ⟨p₁, self_mem_sccOf _ _⟩ ⟨p₂, p2_mem_scc 2⟩
  rw [DC_apply, lift_p1_p2] at this
  omega

theorem lane2_props : ¬ AutoMono (laneAuto 2) ∧ ¬ H2Prod (laneAuto 2) :=
  ⟨lane2_not_autoMono, lane2_not_h2Prod⟩

/-- This agrees with the contrapositive of `h2Core`: `¬ H2Prod` implies `¬ AutoMono`. -/
example : ¬ AutoMono (laneAuto 2) := fun h => lane2_not_h2Prod (h2Core _ _ h)

end Collatz.Arctic.NatQ5.W2e.NonVacuity
