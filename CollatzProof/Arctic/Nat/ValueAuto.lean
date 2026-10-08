/-
# 𝒯: the form of value automata and general families of matrices (Definition 10.1 and Lemma 10.3 of the paper)

Notation partly follows an earlier written argument; the paper writes a value automaton as `(u, N₀, N₁, c)` (Definition 10.1).

* **General families of matrices** (§2): non-negative integer matrices `N : Letter → Matrix ι ι ℕ` (7 letters) on a finite type of indices `ι`. Products of words are
  `N_w := N_{w₁} ⋯ N_{w_k}` (`NW`, in the order of the paper; the empty word gives the identity matrix). Weak orientation of a rule is `N_ℓ ≥ N_r` entrywise
  (`GWeak`, condition (G1) of the paper). The value for fixed indices `a, z` is `(N_{can n})_{az}`. The version of Lemma 10.2 (iii) for general families is
  `gnw_can_T_le` (`(N_{can (T n)})_{az} ≤ (N_{can n})_{az}`, `n ≥ 2`).
* **Value automata** (§3): `ValAuto Q` (the matrices `B₀, B₁` of the binary digits, the initial row vector `u` and the final column vector `v`) and
  the value `aval A ω = u^T B_ω v` (`B_ω` is `Rigid.DxN` of `Nat/RigidDefs.lean`). `ω` is `binWord n` (the binary digits without the leading 1,
  from the most significant one, as a word over `Fin 2`). The value of a general family is the value of an automaton (`nw_can_eq_aval`): `B_b := N_{bit b}`, `u := e_a^T N_{/}`,
  `v := N_{.} e_z`.
* **Natural-number matrix interpretations** (§4): the homogeneous `(d+1)`-dimensional matrices `homN` of `evN` (the type of indices is `Option (Fin d)`; `none` is the homogeneous index `d`,
  `some i` is the index `i`). `homN (evN I w) = NW (homFam I) w` (`homN_evN`). `PhiN I w` is `(N_w)_{(some 0), none}`
  (`phiN_eq_nw`), and `NWeak I ρ` is equivalent to the entrywise inequality of the rule for the homogeneous matrices (`nweak_iff_gweak`).
  The form of a value automaton: `PhiN I (can n) = u^T N_{ω₁} ⋯ N_{ω_N} v` (`phiN_can_eq_aval`, `natAuto I`).
  `u = (row 0 of M_/, (v_/)_0)`, `v = (v_., 1)` (`natAuto_u_some`, `natAuto_u_none`, `natAuto_v_some`, `natAuto_v_none`).

This is the form `\hat u := e_0^T H_&`, `\hat v := H_$ e_d`, `Φ(n) = \hat u B_{bin'(n)} \hat v` of the earlier written argument. In the canonical string
`can n = / bin'(n) .` the only digit letters are `f` (= 0) and `t` (= 1); the ternary digits `d0..d2` do not occur (`binTail_eq`).
-/
import CollatzProof.Arctic.Nat.BridgeTop
import CollatzProof.Arctic.Nat.RigidDefs

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Matrix

set_option linter.unusedSectionVars false

/-! ## §1 Monotonicity of products of non-negative matrices -/

section Mono

variable {ι : Type*} [Fintype ι]

/-- Entrywise inequalities are preserved by multiplying with non-negative matrices from the left and from the right. -/
theorem mul_le_mul_entry {P A A' : Matrix ι ι ℕ} (h : ∀ i j, A i j ≤ A' i j) (i j : ι) :
    (P * A) i j ≤ (P * A') i j := by
  simp only [Matrix.mul_apply]
  exact Finset.sum_le_sum fun k _ => Nat.mul_le_mul_left _ (h k j)

theorem mul_le_mul_entry_right {A A' Q : Matrix ι ι ℕ} (h : ∀ i j, A i j ≤ A' i j) (i j : ι) :
    (A * Q) i j ≤ (A' * Q) i j := by
  simp only [Matrix.mul_apply]
  exact Finset.sum_le_sum fun k _ => Nat.mul_le_mul_right _ (h i k)

end Mono

/-! ## §2 General families of matrices -/

section Gen

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The product of a word `N_w := N_{w₁} ⋯ N_{w_k}` (in the order of the paper; the empty word gives the identity matrix). -/
def NW (N : Letter → Matrix ι ι ℕ) (w : Word) : Matrix ι ι ℕ := (w.map N).prod

@[simp] theorem NW_nil (N : Letter → Matrix ι ι ℕ) : NW N [] = 1 := rfl

theorem NW_cons (N : Letter → Matrix ι ι ℕ) (s : Letter) (w : Word) : NW N (s :: w) = N s * NW N w := by
  simp [NW]

theorem NW_append (N : Letter → Matrix ι ι ℕ) (u w : Word) : NW N (u ++ w) = NW N u * NW N w := by
  simp [NW, List.prod_append]

theorem NW_singleton (N : Letter → Matrix ι ι ℕ) (s : Letter) : NW N [s] = N s := by simp [NW]

/-- Weak orientation for general families (condition (G1) of the paper): `N_ℓ ≥ N_r` entrywise. -/
def GWeak (N : Letter → Matrix ι ι ℕ) (ρ : Rule) : Prop := ∀ i j, NW N ρ.rhs i j ≤ NW N ρ.lhs i j

instance (N : Letter → Matrix ι ι ℕ) (ρ : Rule) : Decidable (GWeak N ρ) :=
  @Fintype.decidableForallFintype _ _
    (fun _ => @Fintype.decidableForallFintype _ _ (fun _ => inferInstance) _) _

/-- One step by a weakly oriented rule does not increase the product of the word, entrywise. -/
theorem nw_step_le {N : Letter → Matrix ι ι ℕ} {ρ : Rule} (hw : GWeak N ρ) (p q : Word) (i j : ι) :
    NW N (p ++ ρ.rhs ++ q) i j ≤ NW N (p ++ ρ.lhs ++ q) i j := by
  rw [NW_append, NW_append, NW_append, NW_append]
  exact mul_le_mul_entry_right (fun i j => mul_le_mul_entry hw i j) i j

/-- Along derivations by weakly oriented rules only, the product of the word does not increase, entrywise. -/
theorem nw_chain_le (N : Letter → Matrix ι ι ℕ) :
    ∀ {rs : List Rule} {u v : Word}, Chain rs u v → (∀ σ ∈ rs, GWeak N σ) → ∀ i j, NW N v i j ≤ NW N u i j := by
  intro rs u v hc
  induction hc with
  | nil u => intro _ _ _; exact le_rfl
  | @cons σ rs u w v hstep _ ih =>
    intro hw i j
    obtain ⟨p, q, rfl, rfl⟩ := hstep
    exact (ih (fun τ hτ => hw τ (List.mem_cons_of_mem _ hτ)) i j).trans
      (nw_step_le (hw σ List.mem_cons_self) p q i j)

/-- **The version of Lemma 10.2 (iii) for general families**: for a family that weakly orients all 11 rules,
`(N_{can (T n)})_{ij} ≤ (N_{can n})_{ij}` for `n ≥ 2` (for all `i, j`). -/
theorem gnw_can_T_le {N : Letter → Matrix ι ι ℕ} (hweak : ∀ ρ ∈ rulesST, GWeak N ρ) (n : ℕ) (hn : 2 ≤ n)
    (i j : ι) : NW N (can (T n)) i j ≤ NW N (can n) i j :=
  nw_chain_le N (canDeriv_chain n hn) (fun σ hσ => hweak σ (canDeriv_sub n σ hσ)) i j

/-- On a segment of an orbit (all points at least 2), `(N_{can ·})_{ij}` does not increase. -/
theorem gnw_can_iterate_le {N : Letter → Matrix ι ι ℕ} (hweak : ∀ ρ ∈ rulesST, GWeak N ρ) (i j : ι) :
    ∀ (m n : ℕ), (∀ k < m, 2 ≤ T^[k] n) → NW N (can (T^[m] n)) i j ≤ NW N (can n) i j := by
  intro m
  induction m with
  | zero => intro n _; simp
  | succ m ih =>
    intro n horb
    have hn : 2 ≤ n := by simpa using horb 0 (Nat.succ_pos m)
    have horb' : ∀ k < m, 2 ≤ T^[k] (T n) := by
      intro k hk
      have := horb (k + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    rw [Function.iterate_succ_apply]
    exact (ih (T n) horb').trans (gnw_can_T_le hweak n hn i j)

end Gen

/-! ## §3 Value automata -/

/-- The letter of a binary digit `b ∈ {0, 1}` (`0 ↦ f`, `1 ↦ t`). -/
def bitLetter (b : Fin 2) : Letter := if b = 0 then Letter.f else Letter.t

@[simp] theorem bitLetter_zero : bitLetter 0 = Letter.f := rfl
@[simp] theorem bitLetter_one : bitLetter 1 = Letter.t := rfl

/-- `bin'(n)`: the binary digits without the leading 1 (from the most significant one), as a word over `Fin 2`. -/
def binWord (n : ℕ) : List (Fin 2) :=
  ((Nat.digits 2 n).reverse.drop 1).map (fun b => if b = 0 then 0 else 1)

/-- The digit part of a canonical string consists of the letters of `binWord` (`f` and `t` only). -/
theorem binTail_eq (n : ℕ) : binTail n = (binWord n).map bitLetter := by
  unfold binTail binWord
  rw [List.map_map]
  congr 1
  funext b
  by_cases hb : b = 0 <;> simp [hb, bitLetter, Function.comp]

theorem can_eq (n : ℕ) : can n = Letter.lft :: ((binWord n).map bitLetter ++ [Letter.rgt]) := by
  rw [can, binTail_eq]

/-- Value automata: a type of indices `Q`, the matrices `B₀, B₁` of the binary digits, the initial row vector `u` and the final column vector `v`
(`N₀, N₁`, `u` and `c` of Definition 10.1 of the paper). -/
structure ValAuto (Q : Type*) where
  B : Fin 2 → Matrix Q Q ℕ
  u : Q → ℕ
  v : Q → ℕ

section Auto

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The value `u^T B_{ω₁} ⋯ B_{ω_N} v` of an automaton (`B_ω` is `Rigid.DxN` of `Nat/RigidDefs.lean`). -/
def aval (A : ValAuto Q) (ω : List (Fin 2)) : ℕ := A.u ⬝ᵥ (Rigid.DxN A.B ω *ᵥ A.v)

theorem aval_eq_sum (A : ValAuto Q) (ω : List (Fin 2)) :
    aval A ω = ∑ i, ∑ j, A.u i * Rigid.DxN A.B ω i j * A.v j := by
  simp only [aval, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

@[simp] theorem DxN_nil' (D : Fin 2 → Matrix Q Q ℕ) : Rigid.DxN D [] = 1 := rfl

theorem DxN_cons' (D : Fin 2 → Matrix Q Q ℕ) (b : Fin 2) (w : List (Fin 2)) :
    Rigid.DxN D (b :: w) = D b * Rigid.DxN D w := by
  simp [Rigid.DxN]

theorem DxN_append' (D : Fin 2 → Matrix Q Q ℕ) (u w : List (Fin 2)) :
    Rigid.DxN D (u ++ w) = Rigid.DxN D u * Rigid.DxN D w := by
  simp [Rigid.DxN, List.prod_append]

/-- For words of digits only, the product of a general family is the product of the digit matrices. -/
theorem NW_map_bit (N : Letter → Matrix Q Q ℕ) (ω : List (Fin 2)) :
    NW N (ω.map bitLetter) = Rigid.DxN (fun b => N (bitLetter b)) ω := by
  induction ω with
  | nil => rfl
  | cons b ω ih => rw [List.map_cons, NW_cons, ih, DxN_cons']

/-- From a general family to a value automaton: `B_b := N_{bit b}`, `u := e_a^T N_/`, `v := N_. e_z`. -/
def genAuto (N : Letter → Matrix Q Q ℕ) (a z : Q) : ValAuto Q where
  B b := N (bitLetter b)
  u j := N Letter.lft a j
  v i := N Letter.rgt i z

/-- **The form of a value automaton (general families)**: `(N_{can n})_{az} = u^T B_{bin'(n)} v`. -/
theorem nw_can_eq_aval (N : Letter → Matrix Q Q ℕ) (a z : Q) (n : ℕ) :
    NW N (can n) a z = aval (genAuto N a z) (binWord n) := by
  rw [can_eq, NW_cons, NW_append, NW_map_bit, NW_singleton, aval]
  simp only [Matrix.mul_apply, dotProduct, mulVec, genAuto, Finset.mul_sum]

end Auto

/-! ## §4 The homogeneous matrices of natural-number matrix interpretations -/

section Hom

variable {d : ℕ}

/-- The homogeneous `(d+1)`-dimensional matrix `\begin{pmatrix} M & v \\ 0 & 1 \end{pmatrix}`. The type of indices is `Option (Fin d)`; `none` is
the homogeneous index (`d` in the earlier notation) and `some i` is the index `i`. -/
def homN (F : NAff d) : Matrix (Option (Fin d)) (Option (Fin d)) ℕ := fun p q =>
  match p, q with
  | some i, some j => F.M i j
  | some i, none => F.v i
  | none, some _ => 0
  | none, none => 1

@[simp] theorem homN_some_some (F : NAff d) (i j : Fin d) : homN F (some i) (some j) = F.M i j := rfl
@[simp] theorem homN_some_none (F : NAff d) (i : Fin d) : homN F (some i) none = F.v i := rfl
@[simp] theorem homN_none_some (F : NAff d) (j : Fin d) : homN F none (some j) = 0 := rfl
@[simp] theorem homN_none_none (F : NAff d) : homN F none none = 1 := rfl

/-- Row `d` (the row of `none`) of a homogeneous matrix is `e_d^T` (the homogeneous index is a sink). -/
theorem homN_none (F : NAff d) (q : Option (Fin d)) : homN F none q = if q = none then 1 else 0 := by
  cases q <;> rfl

theorem homN_comp (F G : NAff d) : homN (F.comp G) = homN F * homN G := by
  ext p q
  cases p with
  | none =>
    cases q <;> simp [Matrix.mul_apply, Fintype.sum_option]
  | some i =>
    cases q with
    | none =>
      simp [Matrix.mul_apply, Fintype.sum_option, NAff.comp, mulVec, dotProduct, add_comm]
    | some j =>
      simp [Matrix.mul_apply, Fintype.sum_option, NAff.comp]

theorem homN_id : homN (NAff.id d) = 1 := by
  ext p q
  cases p <;> cases q <;> simp [NAff.id, Matrix.one_apply]

/-- The family of homogeneous matrices of a natural-number matrix interpretation. -/
def homFam (I : Letter → NAff d) : Letter → Matrix (Option (Fin d)) (Option (Fin d)) ℕ := fun s => homN (I s)

/-- The homogeneous matrix of `evN` is the product of the word of homogeneous matrices. -/
theorem homN_evN (I : Letter → NAff d) : ∀ w : Word, homN (evN I w) = NW (homFam I) w
  | [] => homN_id
  | s :: w => by rw [evN, homN_comp, homN_evN I w, NW_cons]; rfl

/-- Row `d` of the product of a word of homogeneous matrices is `e_d^T`. -/
theorem nw_homFam_none (I : Letter → NAff d) (w : Word) (q : Option (Fin d)) :
    NW (homFam I) w none q = if q = none then 1 else 0 := by
  rw [← homN_evN, homN_none]

theorem phiN_eq_nw [NeZero d] (I : Letter → NAff d) (w : Word) : PhiN I w = NW (homFam I) w (some 0) none := by
  rw [← homN_evN, phiN_eq]; rfl

/-- **Weak orientation is equivalent to the entrywise inequality of the rule for the homogeneous matrices** (the convention `N_ℓ ≥ N_r`; Lemma 10.3 of the paper). -/
theorem nweak_iff_gweak (I : Letter → NAff d) (ρ : Rule) : NWeak I ρ ↔ GWeak (homFam I) ρ := by
  unfold NWeak GWeak
  simp only [← homN_evN]
  constructor
  · rintro ⟨hM, hv⟩ p q
    cases p with
    | none => rw [homN_none, homN_none]
    | some i =>
      cases q with
      | none => exact hv i
      | some j => exact hM i j
  · intro h
    exact ⟨fun i j => h (some i) (some j), fun i => h (some i) none⟩

/-- From weak orientation, the entrywise inequality of the rule for the homogeneous matrices. -/
theorem gweak_of_nweak {I : Letter → NAff d} {ρ : Rule} (h : NWeak I ρ) : GWeak (homFam I) ρ :=
  (nweak_iff_gweak I ρ).1 h

/-- The value automaton of a natural-number matrix interpretation: the type of indices is `Option (Fin d)`, `a := some 0` (the index 0), `z := none`
(the homogeneous index). -/
def natAuto [NeZero d] (I : Letter → NAff d) : ValAuto (Option (Fin d)) := genAuto (homFam I) (some 0) none

/-- **The form of a value automaton (natural-number matrix interpretations)**: `Φ(can n) = u^T N_{ω₁} ⋯ N_{ω_N} v`, `ω = bin'(n)`, where `N_b` is the homogeneous matrix of the
letter of the digit `b`. -/
theorem phiN_can_eq_aval [NeZero d] (I : Letter → NAff d) (n : ℕ) :
    PhiN I (can n) = aval (natAuto I) (binWord n) := by
  rw [phiN_eq_nw, natAuto, nw_can_eq_aval]

@[simp] theorem natAuto_B [NeZero d] (I : Letter → NAff d) (b : Fin 2) :
    (natAuto I).B b = homN (I (bitLetter b)) := rfl

/-- The component of `u` at the index `j` is `(M_/)_{0j}`. -/
@[simp] theorem natAuto_u_some [NeZero d] (I : Letter → NAff d) (j : Fin d) :
    (natAuto I).u (some j) = (I Letter.lft).M 0 j := rfl

/-- The homogeneous component of `u` is `(v_/)_0`. -/
@[simp] theorem natAuto_u_none [NeZero d] (I : Letter → NAff d) : (natAuto I).u none = (I Letter.lft).v 0 := rfl

/-- The component of `v` at the index `i` is `(v_.)_i`. -/
@[simp] theorem natAuto_v_some [NeZero d] (I : Letter → NAff d) (i : Fin d) :
    (natAuto I).v (some i) = (I Letter.rgt).v i := rfl

/-- The homogeneous component of `v` is 1. -/
@[simp] theorem natAuto_v_none [NeZero d] (I : Letter → NAff d) : (natAuto I).v none = 1 := rfl

/-- If the interpretation is monotone, the diagonal entries at the index 0 of the digit matrices are at least 1 (one instance of the condition (G2) of the earlier written argument). The diagonal entry at the homogeneous index is 1 regardless of monotonicity. -/
theorem natAuto_diag [NeZero d] (I : Letter → NAff d) (b : Fin 2) :
    (natAuto I).B b none none = 1 := rfl

theorem natAuto_diag0 [NeZero d] {I : Letter → NAff d} (hmono : NMono I) (b : Fin 2) :
    1 ≤ (natAuto I).B b (some 0) (some 0) := hmono _

end Hom

end Collatz.Arctic.NatQ5
