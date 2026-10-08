/-
# Natural-number matrix interpretations ($\mathcal T$): non-vacuity checks for the definitions of Section 10 of the paper

For the new definitions (`ValueAuto`, `Embed`, `Compartment`, `Lift`, `AutoCore`): their premises can be satisfied, the premises fail on examples on the side
where the conclusion is false, and the value embedding (Lemma 10.5 of the paper) is not trivial. Outside the closure of the main theorems. Computations use `decide +kernel`.

* §1 Premises for general families: `homFam IP3` (affine) and the **non-affine family** `NRev` (the transposes of the homogeneous matrices of the interpretation of dimension 1 that weakly orients $\mathcal T^{\mathrm{rev}}$,
  `[f] = y`, `[t] = [d_i] = 1`, `[/] = 0`, `[.] = y`; the co-affine form of Lemma 10.4 of the paper, `a = 1`, `z = 0`).
  `NRev` weakly orients the 11 rules entrywise, its value `(N_{can n})_{10}` is 0 if `n` is a power of 2 and 1 otherwise (`NRev_values`),
  and it has no sink index (`NRev_no_sink`).
* §2 The value embedding is not trivial: the embedding of `NRev` is a monotone affine interpretation of dimension 3 that weakly orients the 11 rules, and its value is that of `NRev`
  (not constant). So the value of an interpretation of the reversed system becomes the value of a monotone interpretation of the forward system. The value of the embedding of the homogeneous matrices of `IP3` is `Φ_{IP3}`
  (3, 5, 9, 17, growing with the length). The embedding does not preserve strict orientation: the non-monotone `INoMono` strictly orients 8 rules, but
  its embedding strictly orients no rule (`embInterp_not_strict`). `IP3` has the form of a source (the premise of `NatValueCoreSrc`).
* §3 Types of components and (A^rel): one-state automata of the types (Z), (P), (L) and (Hb) (`A1`, `A2`, `A0`, `AH`). `A1` satisfies (A^rel), and
  the heavy component `AH` (not survivable, `ρ(A_C) = 2`, bounded complexity) does not satisfy (A^rel) (`not_aRel_AH`).
* §4 The lift: the value of `liftT A1` is `[3 ∤ n]`. The value of the lift is not monotone on multiples of 3 (`\tilde V(3) = 0 < \tilde V(5)`,
  `not_autoMono_liftT_A1`), so `AutoMono3` (monotonicity on the numbers not divisible by 3) is the correct form.
* §5 Premises of `AutoValueCore`: `natAuto IP3` satisfies (G2) and the monotonicity of the values.
-/
import CollatzProof.Arctic.Nat.AutoCore
import CollatzProof.Arctic.Nat.NonVacuity3

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Matrix Letter

/-! ## §1 Premises for general families -/

theorem homFam_IP3_weak : ∀ ρ ∈ rulesST, GWeak (homFam IP3) ρ := fun ρ hρ => gweak_of_nweak (IP3_weak ρ hρ)

/-- A co-affine family (the transposes of the homogeneous matrices of the interpretation of dimension 1 that weakly orients $\mathcal T^{\mathrm{rev}}$). Index 1 is the source (the transposed homogeneous index). -/
def NRev : Letter → Matrix (Fin 2) (Fin 2) ℕ
  | .f => !![1, 0; 0, 1]
  | .t => !![0, 0; 1, 1]
  | .d0 => !![0, 0; 1, 1]
  | .d1 => !![0, 0; 1, 1]
  | .d2 => !![0, 0; 1, 1]
  | .lft => !![0, 0; 0, 1]
  | .rgt => !![1, 0; 0, 1]

theorem NRev_weak : ∀ ρ ∈ rulesST, GWeak NRev ρ := by decide +kernel

/-- The value `(N_{can n})_{10}`: 0 at powers of 2, 1 otherwise (`Φ^rev`). -/
theorem NRev_values : NW NRev (can 2) 1 0 = 0 ∧ NW NRev (can 3) 1 0 = 1 ∧ NW NRev (can 4) 1 0 = 0 ∧
    NW NRev (can 5) 1 0 = 1 ∧ NW NRev (can 8) 1 0 = 0 ∧ NW NRev (can 12) 1 0 = 1 := by
  decide +kernel

/-- `NRev` is not of affine form: no index is a sink (with row `e_h^T`). -/
theorem NRev_no_sink : ∀ h : Fin 2, ∃ x j, NRev x h j ≠ if j = h then 1 else 0 := by
  have : ∀ h : Fin 2, NRev .t h 0 ≠ if (0 : Fin 2) = h then 1 else 0 := by decide +kernel
  exact fun h => ⟨.t, 0, this h⟩

/-! ## §2 The value embedding is not trivial -/

/-- The embedding of `NRev` is a monotone affine interpretation of dimension 3 that weakly orients the 11 rules, and its values are not constant (0, 1, 0, 1). -/
theorem embInterp_NRev :
    NMono (embInterp NRev 1 0) ∧ (∀ ρ ∈ rulesST, NWeak (embInterp NRev 1 0) ρ) ∧
      PhiN (embInterp NRev 1 0) (can 2) = 0 ∧ PhiN (embInterp NRev 1 0) (can 3) = 1 ∧
      PhiN (embInterp NRev 1 0) (can 4) = 0 ∧ PhiN (embInterp NRev 1 0) (can 5) = 1 := by
  refine ⟨embInterp_mono _ _ _, embInterp_weak _ _ _ NRev_weak, ?_⟩
  simp only [embInterp_phi]
  exact ⟨NRev_values.1, NRev_values.2.1, NRev_values.2.2.1, NRev_values.2.2.2.1⟩

/-- The value of the embedding of the homogeneous matrices of `IP3` is `Φ_{IP3}` (growing with the length on `3 ∣ n`). -/
theorem embInterp_IP3 :
    NMono (embInterp (homFam IP3) (some 0) none) ∧ (∀ ρ ∈ rulesST, NWeak (embInterp (homFam IP3) (some 0) none) ρ) ∧
      PhiN (embInterp (homFam IP3) (some 0) none) (can 3) = 3 ∧
      PhiN (embInterp (homFam IP3) (some 0) none) (can 6) = 5 ∧
      PhiN (embInterp (homFam IP3) (some 0) none) (can 12) = 9 ∧
      PhiN (embInterp (homFam IP3) (some 0) none) (can 24) = 17 := by
  refine ⟨embInterp_mono _ _ _, embInterp_weak _ _ _ homFam_IP3_weak, ?_⟩
  simp only [embInterp_phi, ← phiN_eq_nw]
  exact ⟨IP3_phi_values.1, IP3_phi_values.2.1, IP3_phi_values.2.2.1, IP3_phi_values.2.2.2.1⟩

/-- The embedding does not preserve strict orientation: `INoMono` strictly orients the 2 dynamic rules and the 6 rules of `A`, but its embedding (monotone)
strictly orients no rule. -/
theorem embInterp_loses_strict :
    (∀ ρ ∈ dynST ++ aST, NStrict INoMono ρ) ∧ NMono (embInterp (homFam INoMono) (some 0) none) ∧
      ∀ ρ ∈ rulesST, ¬ NStrict (embInterp (homFam INoMono) (some 0) none) ρ :=
  ⟨INoMono_strict, embInterp_mono _ _ _, embInterp_not_strict _ _ _⟩

/-- `IP3` has the form of a source (the premise of `NatValueCoreSrc`: the diagonal entry at index 0 is exactly 1, and no edge enters 0 from another index). -/
theorem IP3_src : (∀ s, (IP3 s).M 0 0 = 1) ∧ ∀ s (i : Fin 4), i ≠ 0 → (IP3 s).M i 0 = 0 :=
  ⟨fun s => by cases s <;> decide +kernel, fun s => by cases s <;> decide +kernel⟩

/-! ## §3 Types of components and (A^rel) -/

/-- A one-state automaton (digit matrices `B₀ = x`, `B₁ = y`, `û = v̂ = 1`). -/
def auto1 (x y : ℕ) : ValAuto Unit where
  B b := fun _ _ => if b = 0 then x else y
  u _ := 1
  v _ := 1

theorem auto1_B0 (x y : ℕ) (p q : Unit) : (auto1 x y).B 0 p q = x := rfl
theorem auto1_B1 (x y : ℕ) (p q : Unit) : (auto1 x y).B 1 p q = y := rfl

theorem auto1_DxN (x y : ℕ) (w : List (Fin 2)) :
    Rigid.DxN (auto1 x y).B w () () = x ^ w.count 0 * y ^ w.count 1 := by
  induction w with
  | nil => simp
  | cons b w ih =>
    rw [DxN_cons', Matrix.mul_apply, Fintype.sum_unique]
    change (auto1 x y).B b () () * Rigid.DxN (auto1 x y).B w () () = _
    rw [ih]
    fin_cases b
    · simp only [Fin.zero_eta, auto1_B0, List.count_cons_self, pow_succ]
      rw [List.count_cons_of_ne (by decide)]; ring
    · simp only [Fin.mk_one, auto1_B1, List.count_cons_self, pow_succ]
      rw [List.count_cons_of_ne (by decide)]; ring

theorem rel_auto1 (x y : ℕ) : Rel (auto1 x y) () :=
  ⟨⟨(), le_rfl, conn_refl _ ()⟩, ⟨(), conn_refl _ (), le_rfl⟩⟩

theorem DC_auto1 (x y : ℕ) (w : List (Fin 2)) (p q : sccOf (auto1 x y) ()) :
    DC (auto1 x y) (sccOf (auto1 x y) ()) w p q = x ^ w.count 0 * y ^ w.count 1 := by
  rw [DC_apply, auto1_DxN]

theorem AC_auto1 (x y : ℕ) (p q : sccOf (auto1 x y) ()) : AC (auto1 x y) (sccOf (auto1 x y) ()) p q = x + y :=
  rfl

theorem esum_AC_pow_auto1 (x y L : ℕ) : esum (AC (auto1 x y) (sccOf (auto1 x y) ()) ^ L) = (x + y) ^ L := by
  have hC : sccOf (auto1 x y) () = Finset.univ := Finset.eq_univ_of_forall fun u => by
    cases u; exact self_mem_sccOf _ ()
  have hone : ∀ X : Matrix (sccOf (auto1 x y) ()) (sccOf (auto1 x y) ()) ℕ, ∀ p q, X p q = X ⟨(), self_mem_sccOf _ ()⟩ ⟨(), self_mem_sccOf _ ()⟩ := by
    intro X p q
    obtain ⟨⟨⟩, _⟩ := p; obtain ⟨⟨⟩, _⟩ := q; rfl
  have hpow : ∀ L, (AC (auto1 x y) (sccOf (auto1 x y) ()) ^ L) ⟨(), self_mem_sccOf _ ()⟩ ⟨(), self_mem_sccOf _ ()⟩ =
      (x + y) ^ L := by
    intro L
    induction L with
    | zero => simp
    | succ L ih =>
      rw [pow_succ, Matrix.mul_apply, Fintype.sum_eq_single ⟨(), self_mem_sccOf _ ()⟩, ih, AC_auto1, pow_succ]
      intro p hp
      exact absurd (by obtain ⟨⟨⟩, _⟩ := p; rfl) hp
  unfold esum
  rw [Fintype.sum_eq_single ⟨(), self_mem_sccOf _ ()⟩, Fintype.sum_eq_single ⟨(), self_mem_sccOf _ ()⟩, hpow]
  · intro p hp; exact absurd (by obtain ⟨⟨⟩, _⟩ := p; rfl) hp
  · intro p hp; exact absurd (by obtain ⟨⟨⟩, _⟩ := p; rfl) hp

theorem hasEdge_auto1 {x y : ℕ} (h : 1 ≤ x) : HasEdge (auto1 x y) (sccOf (auto1 x y) ()) :=
  ⟨(), self_mem_sccOf _ (), (), self_mem_sccOf _ (), 0, by simpa [auto1] using h⟩

theorem isComp_auto1 {x y : ℕ} (h : 1 ≤ x) : IsComp (auto1 x y) (sccOf (auto1 x y) ()) :=
  ⟨⟨(), rel_auto1 x y, rfl⟩, hasEdge_auto1 h⟩

/-- Type (Z): `B₀ = B₁ = 1` is survivable and 0/1. -/
theorem typeZ_auto1 : IsComp (auto1 1 1) (sccOf (auto1 1 1) ()) ∧ Survivable (auto1 1 1) (sccOf (auto1 1 1) ()) ∧
    ZeroOne (auto1 1 1) (sccOf (auto1 1 1) ()) := by
  refine ⟨isComp_auto1 le_rfl, fun w h => ?_, fun w p q => by rw [DC_auto1]; simp⟩
  have := congrFun (congrFun h ⟨(), self_mem_sccOf _ ()⟩) ⟨(), self_mem_sccOf _ ()⟩
  rw [DC_auto1, Matrix.zero_apply] at this
  simp at this

/-- Type (P): `B₀ = B₁ = 2` is survivable and not 0/1, and `ρ(A_C) = 4 ≥ 2`. -/
theorem typeP_auto2 : Survivable (auto1 2 2) (sccOf (auto1 2 2) ()) ∧ ¬ ZeroOne (auto1 2 2) (sccOf (auto1 2 2) ()) ∧
    ¬ RhoLt (AC (auto1 2 2) (sccOf (auto1 2 2) ())) 2 := by
  refine ⟨fun w h => ?_, fun h => ?_, fun ⟨L, _, hL⟩ => ?_⟩
  · have := congrFun (congrFun h ⟨(), self_mem_sccOf _ ()⟩) ⟨(), self_mem_sccOf _ ()⟩
    rw [DC_auto1, Matrix.zero_apply] at this
    simp at this
  · have := h [0] ⟨(), self_mem_sccOf _ ()⟩ ⟨(), self_mem_sccOf _ ()⟩
    rw [DC_auto1] at this
    simp at this
  · rw [esum_AC_pow_auto1] at hL
    have : 2 ^ L ≤ (2 + 2) ^ L := Nat.pow_le_pow_left (by norm_num) L
    omega

/-- Type (L): `B₀ = 1`, `B₁ = 0` has the killing word `[1]`, and it is 0/1 with `ρ(A_C) = 1 < 2`. -/
theorem typeL_auto0 : ¬ Survivable (auto1 1 0) (sccOf (auto1 1 0) ()) ∧ ZeroOne (auto1 1 0) (sccOf (auto1 1 0) ()) ∧
    RhoLt (AC (auto1 1 0) (sccOf (auto1 1 0) ())) 2 := by
  refine ⟨fun h => h [1] ?_, fun w p q => ?_, ⟨1, le_rfl, by rw [esum_AC_pow_auto1]; norm_num⟩⟩
  · ext p q; rw [DC_auto1]; simp
  · rw [DC_auto1]; rcases Nat.eq_zero_or_pos (w.count 1) with h | h <;> simp [h, Nat.pos_iff_ne_zero.1]

/-- Heavy component (Hb): `B₀ = 2`, `B₁ = 0` is not survivable, `ρ(A_C) = 2`, and the only word of length `r` in `L*` is `0^r` (bounded complexity). -/
theorem typeHb_autoH : ¬ Survivable (auto1 2 0) (sccOf (auto1 2 0) ()) ∧
    ¬ RhoLt (AC (auto1 2 0) (sccOf (auto1 2 0) ())) 2 ∧ BoundedCx (auto1 2 0) (sccOf (auto1 2 0) ()) := by
  refine ⟨fun h => h [1] ?_, fun ⟨L, _, hL⟩ => ?_, ⟨1, fun r => ?_⟩⟩
  · ext p q; rw [DC_auto1]; simp
  · rw [esum_AC_pow_auto1, Nat.add_zero] at hL; omega
  · classical
    refine (Finset.card_le_one.2 fun x hx y hy => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    have key : ∀ x : Fin r → Fin 2, DC (auto1 2 0) (sccOf (auto1 2 0) ()) (List.ofFn x) ≠ 0 → ∀ i, x i = 0 := by
      intro x hx i
      by_contra hi
      apply hx
      ext p q
      rw [DC_auto1, Matrix.zero_apply]
      have hx1 : x i = 1 := by
        rcases Fin.exists_fin_two.1 ⟨x i, rfl⟩ with h | h
        · exact absurd h hi
        · exact h
      have h1 : 0 < (List.ofFn x).count 1 := List.count_pos_iff.2 (List.mem_ofFn.2 ⟨i, hx1⟩)
      rw [zero_pow (Nat.pos_iff_ne_zero.1 h1), mul_zero]
    funext i
    rw [key x hx i, key y hy i]

/-- Examples of the type predicates: (Z), (P), (L), (Hb). -/
theorem auto1_types : TypeZ (auto1 1 1) (sccOf (auto1 1 1) ()) ∧ TypeP (auto1 2 2) (sccOf (auto1 2 2) ()) ∧
    TypeL (auto1 1 0) (sccOf (auto1 1 0) ()) ∧ TypeHb (auto1 2 0) (sccOf (auto1 2 0) ()) :=
  ⟨⟨typeZ_auto1.2.1, typeZ_auto1.2.2⟩, ⟨typeP_auto2.1, typeP_auto2.2.1⟩, ⟨typeL_auto0.1, typeL_auto0.2.2⟩,
    typeHb_autoH⟩

/-- Bounded complexity is not trivial: for `B₀ = B₁ = 1` there are `2^r` words of length `r` in `L*`. -/
theorem not_boundedCx_auto1 : ¬ BoundedCx (auto1 1 1) (sccOf (auto1 1 1) ()) := by
  classical
  rintro ⟨M, hM⟩
  have hall : ∀ r, ((Finset.univ : Finset (Fin r → Fin 2)).filter
      (fun x => DC (auto1 1 1) (sccOf (auto1 1 1) ()) (List.ofFn x) ≠ 0)) = Finset.univ := by
    intro r
    refine Finset.filter_true_of_mem fun x _ h => ?_
    have := congrFun (congrFun h ⟨(), self_mem_sccOf _ ()⟩) ⟨(), self_mem_sccOf _ ()⟩
    rw [DC_auto1, Matrix.zero_apply] at this
    simp at this
  have h := hM M
  rw [hall, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
  have : M < 2 ^ M := Nat.lt_two_pow_self
  omega

/-- An example of type (Hu) (2 states): `B₀ = J` (all ones), `B₁ = E_{01}`. Killing word `11`, `ρ(A_C) = 1 + √2 ≥ 2` (column sums at least 2),
and every word not containing `11` lies in `L*` (not of bounded complexity). -/
def autoHu : ValAuto (Fin 2) where
  B b := if b = 0 then !![1, 1; 1, 1] else !![0, 1; 0, 0]
  u _ := 1
  v _ := 1

theorem autoHu_cons0 (w : List (Fin 2)) (p q : Fin 2) :
    Rigid.DxN autoHu.B (0 :: w) p q = Rigid.DxN autoHu.B w 0 q + Rigid.DxN autoHu.B w 1 q := by
  rw [DxN_apply_cons, Fin.sum_univ_two]
  fin_cases p <;> simp [autoHu]

theorem autoHu_cons1 (w : List (Fin 2)) (q : Fin 2) :
    Rigid.DxN autoHu.B (1 :: w) 0 q = Rigid.DxN autoHu.B w 1 q := by
  rw [DxN_apply_cons, Fin.sum_univ_two]
  simp [autoHu]

theorem autoHu_L0 : ∀ (r : ℕ) (y : Fin r → Fin 2), (∀ j, y j = 0) → 1 ≤ Rigid.DxN autoHu.B (List.ofFn y) 1 1
  | 0, y, _ => by simp
  | r + 1, y, h => by
    rw [List.ofFn_succ, h 0, autoHu_cons0]
    have := autoHu_L0 r (fun i => y i.succ) (fun j => h _)
    omega

theorem autoHu_L1 : ∀ (r : ℕ) (x : Fin r → Fin 2), (∀ j k, x j = 1 → x k = 1 → j = k) →
    1 ≤ Rigid.DxN autoHu.B (List.ofFn x) 0 1 ∨ 1 ≤ Rigid.DxN autoHu.B (List.ofFn x) 1 1
  | 0, x, _ => by right; simp
  | r + 1, x, h => by
    rw [List.ofFn_succ]
    rcases Fin.exists_fin_two.1 ⟨x 0, rfl⟩ with h0 | h0
    · rw [h0]
      left
      rw [autoHu_cons0]
      have := autoHu_L1 r (fun i => x i.succ) (fun j k hj hk => Fin.succ_injective _ (h _ _ hj hk))
      omega
    · rw [h0]
      left
      rw [autoHu_cons1]
      refine autoHu_L0 r _ fun j => ?_
      rcases Fin.exists_fin_two.1 ⟨x j.succ, rfl⟩ with hj | hj
      · exact hj
      · exact absurd (h _ _ h0 hj) (Fin.succ_ne_zero j).symm

theorem autoHu_mem (i : Fin 2) : i ∈ sccOf autoHu 0 := by
  have h01 : Conn autoHu 0 1 := conn_of_edge autoHu (b := 1) (by simp [autoHu])
  have h10 : Conn autoHu 1 0 := conn_of_edge autoHu (b := 0) (by simp [autoHu])
  rw [mem_sccOf]
  fin_cases i
  · exact ⟨conn_refl _ 0, conn_refl _ 0⟩
  · exact ⟨h01, h10⟩

/-- **Type (Hu)**: a component that is not survivable, has `ρ(A_C) ≥ 2`, and is not of bounded complexity. -/
theorem typeHu_autoHu : IsComp autoHu (sccOf autoHu 0) ∧ TypeHu autoHu (sccOf autoHu 0) := by
  have hC : sccOf autoHu 0 = Finset.univ := Finset.eq_univ_of_forall autoHu_mem
  refine ⟨⟨⟨0, ⟨⟨0, le_rfl, conn_refl _ 0⟩, ⟨0, conn_refl _ 0, le_rfl⟩⟩, rfl⟩,
    ⟨0, autoHu_mem 0, 0, autoHu_mem 0, 0, by simp [autoHu]⟩⟩, ?_, ?_, ?_⟩
  · intro h
    apply h [1, 1]
    ext p q
    rw [DC_apply]
    have : Rigid.DxN autoHu.B [1, 1] = 0 := by decide +kernel
    rw [this]; rfl
  · have : Nonempty (sccOf autoHu 0) := ⟨⟨0, autoHu_mem 0⟩⟩
    refine not_rhoLt_of_colSum fun k => ?_
    show 2 ≤ ∑ i : sccOf autoHu 0, (autoHu.B 0 i.1 k.1 + autoHu.B 1 i.1 k.1)
    rw [Finset.sum_coe_sort (sccOf autoHu 0)
      (fun i => (autoHu.B 0 i k.1 + autoHu.B 1 i k.1)),
      Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => absurd (autoHu_mem x) hx), Fin.sum_univ_two]
    obtain ⟨k, hk⟩ := k
    fin_cases k <;> simp [autoHu]
  · classical
    rintro ⟨M, hM⟩
    let g : Fin (M + 1) → (Fin (M + 1) → Fin 2) := fun i j => if j = i then 1 else 0
    have hg : Function.Injective g := by
      intro i k hik
      have := congrFun hik i
      simp only [g, ite_true] at this
      by_contra hne
      simp [hne] at this
    have hsub : Finset.univ.image g ⊆ (Finset.univ : Finset (Fin (M + 1) → Fin 2)).filter
        (fun x => DC autoHu (sccOf autoHu 0) (List.ofFn x) ≠ 0) := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro h0
      have h1 := autoHu_L1 (M + 1) (g i) (fun j k hj hk => by
        simp only [g] at hj hk
        split_ifs at hj hk with h1 h2 <;> simp_all)
      have e0 := congrFun (congrFun h0 ⟨0, autoHu_mem 0⟩) ⟨1, autoHu_mem 1⟩
      have e1 := congrFun (congrFun h0 ⟨1, autoHu_mem 1⟩) ⟨1, autoHu_mem 1⟩
      rw [DC_apply, Matrix.zero_apply] at e0 e1
      simp only at e0 e1
      omega
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin] at hcard
    have := hM (M + 1)
    omega

/-- `B₀ = B₁ = 1` satisfies (A^rel) (the component is 0/1). -/
theorem aRel_auto1 : ARel (auto1 1 1) := by
  refine aRel_of_zeroOne _ fun C hC w p q => ?_
  obtain ⟨⟨q₀, -, rfl⟩, -⟩ := hC
  obtain ⟨⟨⟩⟩ := q₀
  rw [DC_auto1]; simp

/-- The automaton with a heavy component (`B₀ = 2`, `B₁ = 0`) does not satisfy (A^rel) (`π_C(u*) = log(ρ/2) = 0`). -/
theorem not_aRel_AH : ¬ ARel (auto1 2 0) := by
  rintro ⟨u, hu, h⟩
  have hns := typeHb_autoH.1
  have hz : ¬ (Survivable (auto1 2 0) (sccOf (auto1 2 0) ()) ∧ ZeroOne (auto1 2 0) (sccOf (auto1 2 0) ())) :=
    fun h' => hns h'.1
  have hpi := h () (rel_auto1 2 0) hz
  rw [piNeg_iff_rhoLt _ hu () hns] at hpi
  exact typeHb_autoH.2.1 hpi

/-! ## §4 The lift -/

theorem aval_auto1 (ω : List (Fin 2)) : aval (auto1 1 1) ω = 1 := by
  rw [aval_eq_sum, Fintype.sum_unique, Fintype.sum_unique]
  change (auto1 1 1).u () * Rigid.DxN (auto1 1 1).B ω () () * (auto1 1 1).v () = 1
  rw [auto1_DxN]; simp [auto1]

theorem aval_liftT_auto1 (n : ℕ) (hn : 1 ≤ n) : aval (liftT (auto1 1 1)) (binWord n) = if 3 ∣ n then 0 else 1 := by
  rw [aval_liftT _ n hn, aval_auto1, one_mul]

/-- The value of the lift is not monotone on multiples of 3: `\tilde V(3) = 0`, `\tilde V(T 3) = \tilde V(5) = 1`. -/
theorem not_autoMono_liftT_A1 : ¬ AutoMono (liftT (auto1 1 1)) := by
  intro h
  have := h 3 (by norm_num)
  have hT : T 3 = 5 := by decide
  rw [hT, aval_liftT_auto1 5 (by norm_num), aval_liftT_auto1 3 (by norm_num)] at this
  norm_num at this

theorem autoMono3_liftT_A1 : AutoMono3 (liftT (auto1 1 1)) :=
  liftT_mono3 fun n _ => by rw [aval_auto1, aval_auto1]

/-! ## §5 Premises of `AutoValueCore` -/

theorem natAuto_IP3_premises : AutoG2 (natAuto IP3) ∧ AutoMono (natAuto IP3) ∧ ZeroFree (natAuto IP3) :=
  ⟨natAuto_g2 IP3, natAuto_mono IP3_weak, zeroFree_of_g2 (natAuto_g2 IP3)⟩

theorem genAuto_NRev_mono : AutoMono (genAuto NRev 1 0) := genAuto_mono NRev_weak 1 0

end Collatz.Arctic.NatQ5
