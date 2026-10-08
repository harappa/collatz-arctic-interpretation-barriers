/-
# Natural-number matrix interpretations ($\mathcal T$): non-vacuity checks for idempotent words, sojourns and the decomposition (Sections 12.1–12.3)

The premises of `W3Mon`, `W3Stay` and `W3Decomp` can be satisfied, and their conclusions are not trivial. Outside the closure of the main theorem `allBarriers_final`.
It is in the closure of the root `CollatzProof.Arctic.Paper` of this paper (`NonVacuityW3h2`, which `Paper5` imports, imports this file),
so it is part of this release. Computations by `decide +kernel`.

* §1 **`Θ` is not trivial** (a general monoid): in the group `Multiplicative (ZMod 2)` the minimal ideal is the whole group, `e = 1`, and
  `Θ(1, 1, s') = s'` (`theta_group`). The value of `Θ` depends on the final state `s'`.
* §2 **A series automaton** `autoS` (2 indices, `B₀ = B₁ = [[1,1],[0,1]]`, `u = e₀`, `v = e₁`): the components `{0}` and `{1}` both lie in
  $Q_{\mathrm s}$ (`autoS_inZ`), all components are 0/1 (`autoS_h01`), and the value is `V(ω) = |ω|` (`aval_autoS`; the sum over the crossing positions has
  `|ω|` terms, so the degree of the polynomial bound `entry_poly` is not 0).
* §3 **An automaton with a group and a killed component** `autoG` (3 indices: `{0,1}` is a component of permutations, `B₀` the swap and `B₁` the identity; `{2}` is
  a 0/1 component that is not survivable, with only the self-loop of `B₀`, and `B₁` maps `2 → 0`; `u = e₂`, `v = e₀ + e₁`): all components are 0/1 (`autoG_h01`),
  $0 \in Q_{\mathrm s}$, and `2` is relevant and has an internal edge but is not in $Q_{\mathrm s}$ (`autoG_types`); the monoid $\mathcal M_{\mathrm s}$ is not trivial
  (`muZ [0] ≠ muZ [1]`, `autoG_muZ_ne`); every `u♯` kills the component `{2}`, but `[0]` does not (`autoG_kills`).
* §4 **An example with $Q_{\mathrm s} = ∅$** `autoE` (`autoG` with `v = e₂`): $Q_{\mathrm s}$ is empty (`autoE_noZ`), and the value of a word containing `(u♯)^R` is 0
  (`autoE_zero`, an application of `aval_eq_zero_of_noZ`). The word `[0, 0]`, which does not contain `u♯`, has value 1 (`aval_autoE_00`).
* §5 **`DecompData` can be satisfied**: for the automaton with one state (constant value 1), data with a single skeleton of degree 0 (`decomp_one`).
* §6 **The premises of `DecompStmt` (Proposition 12.11, `W3DecompProof8.decompStmt`) can be satisfied**: for `autoS` (value `V(ω) = |ω|`, a term of degree 1 is
  needed) and `autoG` (`u♯` kills the component outside $Q_{\mathrm s}$), all components are 0/1, `u♯` is obtained from `exists_sharp`, and
  `decompStmt` gives the decomposition data (`decomp_autoS`, `decomp_autoG`). Moved here on 2026-10-07 from a probe file of the working repository
  (internal review: the probe files are not released). The names and statements are unchanged.
-/
import CollatzProof.Arctic.Nat.W3Decomp
import CollatzProof.Arctic.Nat.W3DecompProof8

namespace Collatz.Arctic.NatQ5.W3c.NV

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W3c Matrix
open Collatz.Arctic.MinIdeal (IsIdeal IsMinIdeal BRel)

/-! ## §1 `Θ` is not trivial -/

section Group

abbrev G2 := Multiplicative (ZMod 2)

theorem minIdeal_top : IsMinIdeal (⊤ : Submonoid G2) Set.univ := by
  refine ⟨⟨⟨1, trivial⟩, fun _ _ => trivial, fun _ _ _ _ => ⟨trivial, trivial⟩⟩, ?_⟩
  intro I hI y _
  obtain ⟨x, hx⟩ := hI.1
  have := (hI.2.2 (y * x⁻¹) trivial x hx).1
  simpa using this

/-- In a group, `Θ(1, 1, s') = s'`: the value of `Θ` depends on the final state (`Θ(1,1,g) = g ≠ 1 = Θ(1,1,1)`). -/
theorem theta_group (g : G2) : theta (1 : G2) 1 1 g = g := by
  have := theta_eq minIdeal_top (Set.mem_univ 1) (one_mul 1) (s := 1) (A := 1) trivial trivial (one_mul 1)
    (y₀ := g) (one_mul g)
  simpa using this

theorem theta_group_nontrivial : theta (1 : G2) 1 1 (Multiplicative.ofAdd 1) ≠ theta (1 : G2) 1 1 1 := by
  rw [theta_group, theta_group]; decide

end Group

/-! ## §2 A series automaton -/

section Series

/-- The series automaton: `B₀ = B₁ = [[1,1],[0,1]]`, `u = e₀`, `v = e₁`. -/
def autoS : ValAuto (Fin 2) where
  B _ := !![1, 1; 0, 1]
  u := ![1, 0]
  v := ![0, 1]

theorem autoS_DxN (w : List (Fin 2)) : Rigid.DxN autoS.B w = !![1, w.length; 0, 1] := by
  induction w with
  | nil => ext i j; fin_cases i <;> fin_cases j <;> rfl
  | cons b w ih =>
    rw [DxN_cons', ih]
    show !![1, 1; 0, 1] * !![1, w.length; 0, 1] = !![1, (b :: w).length; 0, 1]
    rw [Matrix.mul_fin_two]
    simp only [List.length_cons]
    congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp

theorem autoS_DxN_10 (w : List (Fin 2)) : Rigid.DxN autoS.B w 1 0 = 0 := by rw [autoS_DxN]; rfl

theorem autoS_scc {q x : Fin 2} (hx : x ∈ sccOf autoS q) : x = q := by
  rw [mem_sccOf] at hx
  obtain ⟨⟨w, hw⟩, ⟨w', hw'⟩⟩ := hx
  by_contra hne
  have key : ∀ a b : Fin 2, a ≠ b → (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by decide
  rcases key x q hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [autoS_DxN_10] at hw'; omega
  · rw [autoS_DxN_10] at hw; omega

theorem autoS_diag (w : List (Fin 2)) (q : Fin 2) : Rigid.DxN autoS.B w q q = 1 := by
  rw [autoS_DxN]; fin_cases q <;> rfl

theorem autoS_rel (q : Fin 2) : Rel autoS q := by
  have h01 : Conn autoS 0 1 := ⟨[0], by rw [autoS_DxN]; decide⟩
  fin_cases q
  · exact ⟨⟨0, by decide, conn_refl _ 0⟩, ⟨1, h01, by decide⟩⟩
  · exact ⟨⟨0, by decide, h01⟩, ⟨1, conn_refl _ 1, by decide⟩⟩

theorem autoS_zeroOne (q : Fin 2) : ZeroOne autoS (sccOf autoS q) := by
  intro w x y
  rw [DC_apply, autoS_scc x.2, autoS_scc y.2, autoS_diag]

/-- All components are 0/1. -/
theorem autoS_h01 : ∀ C, IsComp autoS C → ZeroOne autoS C := by
  rintro C ⟨⟨q, _, rfl⟩, _⟩
  exact autoS_zeroOne q

/-- The two components `{0}` and `{1}` both lie in $Q_{\mathrm s}$. -/
theorem autoS_inZ (q : Fin 2) : InZ autoS q := by
  refine ⟨autoS_rel q, ⟨q, self_mem_sccOf _ q, q, self_mem_sccOf _ q, 0, ?_⟩, fun w h => ?_, autoS_zeroOne q⟩
  · fin_cases q <;> decide
  · have := congrFun (congrFun h ⟨q, self_mem_sccOf _ q⟩) ⟨q, self_mem_sccOf _ q⟩
    rw [DC_apply, Matrix.zero_apply] at this
    have h1 : Rigid.DxN autoS.B w q q = 0 := this
    rw [autoS_diag] at h1
    omega

/-- **The value is `|ω|`**: the sum over the crossing positions has `|ω|` terms (the degree of the polynomial bound is not 0). -/
theorem aval_autoS (ω : List (Fin 2)) : aval autoS ω = ω.length := by
  rw [aval_eq_sum, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, autoS_DxN]
  simp [autoS]

/-- An application of the polynomial bound (`W = 1`, `|Q| = 2`). -/
theorem autoS_poly (ω : List (Fin 2)) : aval autoS ω ≤ 1 * 1 * ((2 ^ 2 * 1 + 1) ^ 2 * (ω.length + 1) ^ 2) := by
  have h := aval_poly autoS autoS_h01 (W := 1) (fun b i j => by
    show (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℕ) i j ≤ 1
    fin_cases i <;> fin_cases j <;> decide) ω
  have hu : ∑ i, autoS.u i = 1 := by simp [autoS, Fin.sum_univ_two]
  have hv : ∑ j, autoS.v j = 1 := by simp [autoS, Fin.sum_univ_two]
  rw [hu, hv, Fintype.card_fin] at h
  exact h

end Series

/-! ## §3 An automaton with a group and a killed component -/

section GroupAuto

/-- The digit matrices: on `{0,1}`, `B₀` is the swap and `B₁` the identity; index 2 has a self-loop under `B₀`, and `B₁` maps `2 → 0`. -/
def BG : Fin 2 → Matrix (Fin 3) (Fin 3) ℕ := fun b =>
  if b = 0 then !![0, 1, 0; 1, 0, 0; 0, 0, 1] else !![1, 0, 0; 0, 1, 0; 1, 0, 0]

/-- `autoG`: `u = e₂`, `v = e₀ + e₁`. -/
def autoG : ValAuto (Fin 3) where
  B := BG
  u := ![0, 0, 1]
  v := ![1, 1, 0]

/-- `autoE`: `u = e₂`, `v = e₂` ($Q_{\mathrm s} = ∅$). -/
def autoE : ValAuto (Fin 3) where
  B := BG
  u := ![0, 0, 1]
  v := ![0, 0, 1]

/-- The permutation on the indices 0 and 1 (`B₀` swaps them, `B₁` is the identity). -/
def pi1 (b : Fin 2) (i : Fin 3) : Fin 3 := if b = 0 then (if i = 0 then 1 else if i = 1 then 0 else i) else i

def piW : List (Fin 2) → Fin 3 → Fin 3
  | [], i => i
  | b :: w, i => piW w (pi1 b i)

theorem pi1_ne_two (b : Fin 2) {i : Fin 3} (hi : i ≠ 2) : pi1 b i ≠ 2 := by
  revert hi; fin_cases b <;> fin_cases i <;> decide

theorem piW_ne_two (w : List (Fin 2)) : ∀ {i : Fin 3}, i ≠ 2 → piW w i ≠ 2 := by
  induction w with
  | nil => intro i hi; exact hi
  | cons b w ih => intro i hi; exact ih (pi1_ne_two b hi)

theorem BG_row (b : Fin 2) {i : Fin 3} (hi : i ≠ 2) (k : Fin 3) : BG b i k = if k = pi1 b i then 1 else 0 := by
  revert hi; fin_cases b <;> fin_cases i <;> fin_cases k <;> decide

/-- The rows leaving the indices 0 and 1 are rows of permutation matrices: `(B_w)_{ij} = [j = π_w(i)]`. -/
theorem BG_DxN (w : List (Fin 2)) : ∀ {i : Fin 3}, i ≠ 2 → ∀ j, Rigid.DxN BG w i j = if j = piW w i then 1 else 0 := by
  induction w with
  | nil => intro i _ j; simp [piW, Matrix.one_apply, eq_comm]
  | cons b w ih =>
    intro i hi j
    rw [DxN_apply_cons, Fintype.sum_eq_single (pi1 b i)]
    · rw [BG_row b hi, ih (pi1_ne_two b hi)]; simp only [↓reduceIte, one_mul]; rfl
    · intro k hk; rw [BG_row b hi]; simp only [hk, ↓reduceIte, zero_mul]

theorem BG_DxN_22 (w : List (Fin 2)) : Rigid.DxN BG w 2 2 ≤ 1 := by
  induction w with
  | nil => simp
  | cons b w ih =>
    rw [DxN_apply_cons]
    fin_cases b
    · rw [Fintype.sum_eq_single 2]
      · simpa [BG] using ih
      · intro k hk; fin_cases k <;> simp_all [BG]
    · rw [Fintype.sum_eq_single 0]
      · rw [BG_DxN w (by decide) 2]
        have := piW_ne_two w (i := 0) (by decide)
        simp [BG, Ne.symm this]
      · intro k hk; fin_cases k <;> simp_all [BG]

theorem BG_not_to_two (w : List (Fin 2)) {i : Fin 3} (hi : i ≠ 2) : Rigid.DxN BG w i 2 = 0 := by
  rw [BG_DxN w hi]; simp [Ne.symm (piW_ne_two w hi)]

section Common

variable {A : ValAuto (Fin 3)} (hB : A.B = BG)
include hB

theorem conn_two_iff {i : Fin 3} (hi : i ≠ 2) : ¬ Conn A i 2 := by
  rintro ⟨w, hw⟩; rw [hB, BG_not_to_two w hi] at hw; omega

theorem scc_two : ∀ x, x ∈ sccOf A 2 → x = 2 := by
  intro x hx
  by_contra hne
  exact conn_two_iff hB hne ((mem_sccOf A).1 hx).2

theorem scc_zero : ∀ x, x ∈ sccOf A 0 → x ≠ 2 := by
  intro x hx hx2
  subst hx2
  exact conn_two_iff hB (by decide) ((mem_sccOf A).1 hx).1

theorem one_mem_scc_zero : (1 : Fin 3) ∈ sccOf A 0 :=
  (mem_sccOf A).2 ⟨⟨[0], by rw [hB]; decide⟩, ⟨[0], by rw [hB]; decide⟩⟩

theorem zeroOne_scc (q : Fin 3) : ZeroOne A (sccOf A q) := by
  intro w x y
  rw [DC_apply, hB]
  by_cases hx : x.1 = 2
  · by_cases hy : y.1 = 2
    · rw [hx, hy]; exact BG_DxN_22 w
    · -- `x = 2` and `y ≠ 2` are not in the same component (`2` is not reachable from `y`)
      exfalso
      have hxy : Conn A y.1 x.1 := conn_of_mem_sccOf A y.2 x.2
      rw [hx] at hxy
      exact conn_two_iff hB hy hxy
  · rw [BG_DxN w hx]; split_ifs <;> simp

theorem h01_of : ∀ C, IsComp A C → ZeroOne A C := by
  rintro C ⟨⟨q, _, rfl⟩, _⟩
  exact zeroOne_scc hB q

theorem hasEdge_two : HasEdge A (sccOf A 2) :=
  ⟨2, self_mem_sccOf A 2, 2, self_mem_sccOf A 2, 0, by rw [hB]; decide⟩

theorem not_survivable_two : ¬ Survivable A (sccOf A 2) := by
  intro h
  apply h [1]
  ext x y
  rw [DC_apply, scc_two hB x.1 x.2, scc_two hB y.1 y.2, hB]
  rfl

theorem not_inZ_two : ¬ InZ A 2 := fun h => not_survivable_two hB h.2.2.1

end Common

theorem autoG_rel (q : Fin 3) : Rel autoG q := by
  have h20 : Conn autoG 2 0 := ⟨[1], by decide⟩
  have h01 : Conn autoG 0 1 := ⟨[0], by decide⟩
  fin_cases q
  · exact ⟨⟨2, by decide, h20⟩, ⟨0, conn_refl _ 0, by decide⟩⟩
  · exact ⟨⟨2, by decide, conn_trans _ h20 h01⟩, ⟨1, conn_refl _ 1, by decide⟩⟩
  · exact ⟨⟨2, by decide, conn_refl _ 2⟩, ⟨0, h20, by decide⟩⟩

theorem autoG_inZ0 : InZ autoG 0 := by
  have hB : autoG.B = BG := rfl
  refine ⟨autoG_rel 0, ⟨0, self_mem_sccOf _ 0, 1, one_mem_scc_zero hB, 0, by decide⟩, fun w h => ?_,
    zeroOne_scc hB 0⟩
  -- inside the component, the entry `(0, π_w(0))` is 1
  have hmem : piW w 0 ∈ sccOf autoG 0 := by
    have h0 : piW w 0 ≠ 2 := piW_ne_two w (by decide)
    have hc : ∀ x : Fin 3, x ≠ 2 → x ∈ sccOf autoG 0 := by
      intro x hx
      fin_cases x
      · exact self_mem_sccOf _ 0
      · exact one_mem_scc_zero hB
      · exact absurd rfl hx
    exact hc _ h0
  have := congrFun (congrFun h ⟨0, self_mem_sccOf _ 0⟩) ⟨piW w 0, hmem⟩
  rw [DC_apply, Matrix.zero_apply] at this
  have h1 : Rigid.DxN BG w 0 (piW w 0) = 0 := this
  rw [BG_DxN w (by decide)] at h1
  simp at h1

theorem autoG_h01 : ∀ C, IsComp autoG C → ZeroOne autoG C := h01_of rfl

/-- The types of the components of `autoG`: $0 \in Q_{\mathrm s}$; `2` is relevant and has an internal edge (a component) but is not in $Q_{\mathrm s}$ (a 0/1 component that is not survivable). -/
theorem autoG_types : InZ autoG 0 ∧ Rel autoG 2 ∧ IsComp autoG (sccOf autoG 2) ∧ ¬ InZ autoG 2 ∧
    ZeroOne autoG (sccOf autoG 2) :=
  ⟨autoG_inZ0, autoG_rel 2, ⟨⟨2, autoG_rel 2, rfl⟩, hasEdge_two rfl⟩, not_inZ_two rfl, zeroOne_scc rfl 2⟩

theorem autoG_inZ1 : InZ autoG 1 := inZ_of_mem autoG autoG_inZ0 (one_mem_scc_zero rfl)

/-- The monoid $\mathcal M_{\mathrm s}$ is not trivial: `muZ [0]` (the swap) and `muZ [1]` (the identity) differ. -/
theorem autoG_muZ_ne : muZ autoG [0] ≠ muZ autoG [1] := by
  intro h
  have h1 := congrFun (congrFun h ⟨0, autoG_inZ0⟩) ⟨1, autoG_inZ1⟩
  have hl : muZ autoG [0] ⟨0, autoG_inZ0⟩ ⟨1, autoG_inZ1⟩ := ⟨one_mem_scc_zero rfl, by decide⟩
  rw [h1] at hl
  have : ¬ (1 ≤ Rigid.DxN autoG.B [1] 0 1) := by decide
  exact this hl.2

/-- Every `u♯` kills the component `{2}`, but `[0]` does not (killing is not a trivial property). -/
theorem autoG_kills : (∀ K u e, Sharp autoG K u e → DC autoG (sccOf autoG 2) u = 0) ∧
    DC autoG (sccOf autoG 2) [0] ≠ 0 := by
  refine ⟨fun K u e hS => hS.kills autoG autoG_h01 (autoG_rel 2) (not_inZ_two rfl), fun h => ?_⟩
  have := congrFun (congrFun h ⟨2, self_mem_sccOf _ 2⟩) ⟨2, self_mem_sccOf _ 2⟩
  rw [DC_apply, Matrix.zero_apply] at this
  have h1 : Rigid.DxN autoG.B [0] 2 2 = 0 := this
  revert h1; decide

end GroupAuto

/-! ## §4 An example with $Q_{\mathrm s} = ∅$ -/

section Empty

theorem autoE_noZ : ∀ q, ¬ InZ autoE q := by
  intro q hq
  have hB : autoE.B = BG := rfl
  by_cases h2 : q = 2
  · subst h2; exact not_inZ_two hB hq
  · obtain ⟨_, ⟨j, hj, hv⟩⟩ := hq.1
    have hj2 : j = 2 := by
      by_contra hne; fin_cases j <;> simp_all [autoE]
    subst hj2
    exact conn_two_iff hB h2 hj

theorem autoE_h01 : ∀ C, IsComp autoE C → ZeroOne autoE C := h01_of rfl

/-- If $Q_{\mathrm s} = ∅$, the value of a word containing `(u♯)^R` (`R ≥ 3`) is 0. -/
theorem autoE_zero {K : Set (BRel (ZIdx autoE))} {u : List (Fin 2)} {e : BRel (ZIdx autoE)}
    (hS : Sharp autoE K u e) {R : ℕ} (hR : 3 ≤ R) (τ' ρ : List (Fin 2)) :
    aval autoE (τ' ++ (List.replicate R u).flatten ++ ρ) = 0 :=
  aval_eq_zero_of_noZ autoE autoE_h01 hS autoE_noZ (by simpa using hR) τ' ρ

/-- A word that does not contain `u♯` has a non-zero value (the conclusion above is not trivial). -/
theorem aval_autoE_00 : aval autoE [0, 0] = 1 := by decide +kernel

end Empty

/-! ## §5 `DecompData` can be satisfied -/

section Decomp

/-- An automaton with one state (`B₀ = B₁ = 1`, `u = v = 1`, constant value 1). -/
def one1 : ValAuto Unit where
  B _ := fun _ _ => 1
  u _ := 1
  v _ := 1

theorem one1_DxN (w : List (Fin 2)) : Rigid.DxN one1.B w () () = 1 := by
  induction w with
  | nil => simp
  | cons b w ih =>
    rw [DxN_cons', Matrix.mul_apply, Fintype.sum_unique]
    change 1 * Rigid.DxN one1.B w () () = 1
    rw [ih]

theorem aval_one1 (ω : List (Fin 2)) : aval one1 ω = 1 := by
  rw [aval_eq_sum, Fintype.sum_unique, Fintype.sum_unique, one1_DxN]; rfl

/-- Decomposition data with a single skeleton of degree 0 (`κ = 1`). `spec` is closed by `termOf_of_deg_zero`. -/
noncomputable def decomp_one (u τ' y'' z : List (Fin 2)) (R : ℕ) : DecompData one1 u τ' y'' z R where
  Γ := Unit
  finΓ := inferInstance
  deg _ := 0
  t0 _ := 0
  t1 _ := 0
  t0_le _ := Nat.zero_le _
  t1_le _ := Nat.zero_le _
  Lab := Unit
  finLab := inferInstance
  labS _ := 1
  κ _ _ _ := 1
  g _ k := k.elim0
  g_len _ k := k.elim0
  cP := 0
  dP := 0
  g_poly _ k := k.elim0
  cW := 0
  g_free _ k := k.elim0
  spec m := by
    rw [aval_one1, Fintype.sum_unique]
    exact (termOf_of_deg_zero one1 (Lab := Unit) (fun _ => 1) (s := 0) rfl (fun _ _ => 1) (fun k => k.elim0) 0
      _ _ _).symm

theorem decomp_one_nonempty (u τ' y'' z : List (Fin 2)) (R : ℕ) : Nonempty (DecompData one1 u τ' y'' z R) :=
  ⟨decomp_one u τ' y'' z R⟩

end Decomp

/-! ## §6 The premises of `DecompStmt` can be satisfied (moved here on 2026-10-07 from a probe file of the working repository) -/

section DecompStmt

/-- `autoS` (`Q = Fin 2`): `u♯` exists, and decomposition data exist for every `R ≥ 2` (and all `τ'`, `y''`, `z`). -/
theorem decomp_autoS : ∃ K u e, Sharp autoS K u e ∧
    ∀ R, 2 ≤ R → ∀ τ' y'' z : List (Fin 2), Nonempty (DecompData autoS u τ' y'' z R) := by
  obtain ⟨K, u, e, hS⟩ := exists_sharp (A := autoS)
  exact ⟨K, u, e, hS, fun R hR τ' y'' z =>
    decompStmt (Fin 2) autoS autoS_h01 K u e hS R (by simpa using hR) τ' y'' z⟩

/-- `autoG` (`Q = Fin 3`): `u♯` exists, and decomposition data exist for every `R ≥ 3` (and all `τ'`, `y''`, `z`). -/
theorem decomp_autoG : ∃ K u e, Sharp autoG K u e ∧
    ∀ R, 3 ≤ R → ∀ τ' y'' z : List (Fin 2), Nonempty (DecompData autoG u τ' y'' z R) := by
  obtain ⟨K, u, e, hS⟩ := exists_sharp (A := autoG)
  exact ⟨K, u, e, hS, fun R hR τ' y'' z =>
    decompStmt (Fin 3) autoG autoG_h01 K u e hS R (by simpa using hR) τ' y'' z⟩

end DecompStmt

end Collatz.Arctic.NatQ5.W3c.NV
