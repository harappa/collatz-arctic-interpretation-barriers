/-
# Natural-number interpretations of 𝒯 (proof of Proposition 12.11, part 7): the weights of the top and low parts, and cutting the value

Parts of the proof of the frozen statement `DecompStmt` of `W3Decomp.lean`. The assembly is in `W3DecompProof8.lean`.

* **The weights of the top and low parts** `Umat`, `Wmat` (the sums for the parts before and after in `block_first`, `block_last`), and `Uv`, `Wv`, obtained by contracting them with `û`, `v̂`
  (`A.u`, `A.v`; `u`, `c` in the paper). `Uv` depends only on the top part `τ`, and `Wv` only on the shared part `y`.
* **Cutting the value** `aval_blocks`: `V(ω) = Σ_{c₀, c₁} Σ_{j₀, j₁} Uv c₀ j₀ · (D_{u♯} B_{(t₀, t_m]} D_{u♯})_{j₀ j₁} · Wv c₁ j₁`.
* Facts on positions in point words: the copies in the top part and in the shared part, `s_T = s_{t₁}` (`sT_eq`), `firstOcc a₀ = a₀`.
* The decomposition data (skeletons `Γ = Fin R × Q × Fin R × Q × Fin |Q|`, labels `LabT`, `κ = Uv · Wv · [relevant] · thetaChain`,
  `g = gfun`) and `decompStmt` are in `W3DecompProof8.lean`.
-/
import CollatzProof.Arctic.Nat.W3DecompProof6

namespace Collatz.Arctic.NatQ5.W3c

open Collatz.Arctic Collatz.Arctic.NatQ5 Matrix
open Collatz.Arctic.MinIdeal (BRel)

set_option linter.unusedSectionVars false

attribute [local instance] fintypeBRelZ

section Ends

variable {Q : Type} [Fintype Q] [DecidableEq Q] (A : ValAuto Q) (u : List (Fin 2))

open Classical in
/-- The sum for the part before in the top part (every copy `c' < c₀` is broken). -/
noncomputable def Umat (τ' : List (Fin 2)) (R c0 : ℕ) : Matrix Q Q ℕ :=
  ∑ P1 ∈ (Finset.range (τ'.length + c0 * u.length)).powerset.filter
      (fun P => ∀ c' < c0, ¬ Unbroken P τ'.length u.length c'),
    mixAux (Dp A) (Ep A) P1 0 ((topW u τ' R).take (τ'.length + c0 * u.length))

open Classical in
/-- The sum for the part after in the shared part (every copy `c' > c₁` is broken). -/
noncomputable def Wmat (y'' z : List (Fin 2)) (R c1 : ℕ) : Matrix Q Q ℕ :=
  ∑ P2 ∈ (Finset.Ico (y''.length + c1 * u.length + u.length)
      (tailW u y'' z R).length).powerset.filter
      (fun P => ∀ c', c1 < c' → c' < R → ¬ Unbroken P y''.length u.length c'),
    mixAux (Dp A) (Ep A) P2 (y''.length + c1 * u.length + u.length)
      ((tailW u y'' z R).drop (y''.length + c1 * u.length + u.length))

/-- The weight of the top part `Uv c₀ j₀ = (û^T U_{c₀})_{j₀}`. -/
noncomputable def Uv (τ' : List (Fin 2)) (R c0 : ℕ) (j0 : Q) : ℕ := ∑ i, A.u i * Umat A u τ' R c0 i j0

/-- The weight of the low part `Wv c₁ j₁ = (W_{c₁} v̂)_{j₁}`. -/
noncomputable def Wv (y'' z : List (Fin 2)) (R c1 : ℕ) (j1 : Q) : ℕ := ∑ j, Wmat A u y'' z R c1 j1 j * A.v j

theorem conn_of_Umat {τ' : List (Fin 2)} {R c0 : ℕ} {i j : Q} (h : 1 ≤ Umat A u τ' R c0 i j) : Conn A i j := by
  unfold Umat at h
  rw [Matrix.sum_apply] at h
  obtain ⟨P, -, hP⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.one_le_iff_ne_zero.1 h)
  exact conn_of_DxN A (le_trans (Nat.one_le_iff_ne_zero.2 hP) (mixAux_le A P _ 0 i j))

theorem conn_of_Wmat {y'' z : List (Fin 2)} {R c1 : ℕ} {i j : Q} (h : 1 ≤ Wmat A u y'' z R c1 i j) : Conn A i j := by
  unfold Wmat at h
  rw [Matrix.sum_apply] at h
  obtain ⟨P, -, hP⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.one_le_iff_ne_zero.1 h)
  exact conn_of_DxN A (le_trans (Nat.one_le_iff_ne_zero.2 hP) (mixAux_le A P _ _ i j))

end Ends

section Words

variable (u τ' y'' z m : List (Fin 2)) (R : ℕ)

theorem fullW_assoc_top : fullW u τ' y'' z m R = τ' ++ (List.replicate R u).flatten ++ (m ++ tailW u y'' z R) := by
  simp [fullW, topW, List.append_assoc]

theorem fullW_assoc_tail :
    fullW u τ' y'' z m R = (topW u τ' R ++ m ++ y'') ++ (List.replicate R u).flatten ++ z := by
  simp [fullW, tailW, List.append_assoc]

theorem seg_fullW_mid {t0 tm' : ℕ} (h0 : t0 ≤ (topW u τ' R).length) (_h1 : tm' ≤ (tailW u y'' z R).length) :
    seg (fullW u τ' y'' z m R) t0 ((topW u τ' R).length + m.length + tm') =
      (topW u τ' R).drop t0 ++ m ++ (tailW u y'' z R).take tm' := by
  unfold seg fullW
  rw [List.append_assoc, List.drop_append_of_le_length h0, List.take_append, List.take_of_length_le (by simp; omega),
    List.length_drop, List.take_append, List.take_of_length_le (by omega), List.append_assoc]
  congr 3; omega

theorem take_fullW_top {p : ℕ} (hp : p ≤ (topW u τ' R).length) :
    (fullW u τ' y'' z m R).take p = (topW u τ' R).take p := by
  unfold fullW
  rw [List.append_assoc, List.take_append_of_le_length hp]

end Words

section Assemble

variable {Q : Type} [Fintype Q] [DecidableEq Q] {A : ValAuto Q} {u : List (Fin 2)} {K : Set (BRel (ZIdx A))}
  {e : BRel (ZIdx A)}

/-- `û^T (U M W) v̂ = Σ_{j₀} Σ_{j₁} (û^T U)_{j₀} M_{j₀j₁} (W v̂)_{j₁}`. -/
theorem dot_mul3 (U M W : Matrix Q Q ℕ) (uu vv : Q → ℕ) :
    uu ⬝ᵥ ((U * M * W) *ᵥ vv) = ∑ j0, ∑ j1, (∑ i, uu i * U i j0) * M j0 j1 * (∑ j, W j1 j * vv j) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  simp only [dotProduct, mulVec, vecMul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j0 _ => Finset.sum_congr rfl fun j1 _ => ?_
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_assoc]

/-- **Cutting the value** (at the first unbroken copy of the top part and at the last unbroken copy of the shared part). -/
theorem aval_blocks (hS : Sharp A K u e) {R : ℕ} (hR : Fintype.card Q ≤ R) (τ' y'' z m : List (Fin 2)) :
    aval A (fullW u τ' y'' z m R) =
      ∑ c0 ∈ Finset.range R, ∑ c1 ∈ Finset.range R, ∑ j0, ∑ j1,
        Uv A u τ' R c0 j0 *
          (Rigid.DxN (Dp A) u * Rigid.DxN A.B (seg (fullW u τ' y'' z m R) (τ'.length + c0 * u.length + u.length)
              ((topW u τ' R).length + m.length + (y''.length + c1 * u.length))) * Rigid.DxN (Dp A) u) j0 j1 *
          Wv A u y'' z R c1 j1 := by
  have hBτ := block_first A hS hR τ' []
  have hBy := block_last A hS hR y'' z
  have htop : τ' ++ (List.replicate R u).flatten ++ [] = topW u τ' R := by simp [topW]
  have htail : y'' ++ (List.replicate R u).flatten ++ z = tailW u y'' z R := rfl
  rw [htop] at hBτ
  rw [htail] at hBy
  have hlt : (topW u τ' R).length = τ'.length + R * u.length := length_topW u τ' R
  have hly : (tailW u y'' z R).length = y''.length + R * u.length + z.length := length_tailW u y'' z R
  have hB : Rigid.DxN A.B (fullW u τ' y'' z m R) =
      ∑ c0 ∈ Finset.range R, ∑ c1 ∈ Finset.range R,
        Umat A u τ' R c0 * (Rigid.DxN (Dp A) u * Rigid.DxN A.B (seg (fullW u τ' y'' z m R)
          (τ'.length + c0 * u.length + u.length) ((topW u τ' R).length + m.length + (y''.length + c1 * u.length))) *
          Rigid.DxN (Dp A) u) * Wmat A u y'' z R c1 := by
    have e2 : ∀ c0 ∈ Finset.range R, ∀ c1 ∈ Finset.range R,
        Rigid.DxN A.B (seg (fullW u τ' y'' z m R) (τ'.length + c0 * u.length + u.length)
          ((topW u τ' R).length + m.length + (y''.length + c1 * u.length))) =
        Rigid.DxN A.B ((topW u τ' R).drop (τ'.length + c0 * u.length + u.length)) * Rigid.DxN A.B m *
          Rigid.DxN A.B ((tailW u y'' z R).take (y''.length + c1 * u.length)) := by
      intro c0 hc0 c1 hc1
      have hc0L : (c0 + 1) * u.length ≤ R * u.length := Nat.mul_le_mul_right _ (by have := Finset.mem_range.1 hc0; omega)
      have hc1L : (c1 + 1) * u.length ≤ R * u.length := Nat.mul_le_mul_right _ (by have := Finset.mem_range.1 hc1; omega)
      rw [seg_fullW_mid u τ' y'' z m R (by rw [hlt]; nlinarith) (by rw [hly]; nlinarith), DxN_append', DxN_append']
    rw [Finset.sum_congr rfl fun c0 hc0 => Finset.sum_congr rfl fun c1 hc1 => by rw [e2 c0 hc0 c1 hc1]]
    rw [show fullW u τ' y'' z m R = topW u τ' R ++ m ++ tailW u y'' z R from rfl, DxN_append', DxN_append',
      hBτ, hBy, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c0 _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c1 _ => ?_
    simp only [Umat, Wmat, Matrix.mul_assoc]
  unfold aval
  rw [hB, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun c0 _ => ?_
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun c1 _ => ?_
  rw [dot_mul3]
  rfl

end Assemble

end Collatz.Arctic.NatQ5.W3c
