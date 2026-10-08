/-
# Natural-number interpretations of 𝒯 (proof of Proposition 12.11, part 8): the proof of `DecompStmt`

* Facts on positions in the point word `ω = τ'(u♯)^R m y''(u♯)^R z`: the copies in the top part (`copy_top`) and in the shared part (`copy_tail`),
  `firstOcc a₀ = a₀`, `s_T = s_{t₁}` (`sT_eq`).
* Terms with indices that are not relevant vanish (`rel_of_uv_mid_wv`).
* Agreement for each skeleton (`term_gamma`): `termOf(γ) = Uv · Wv · [relevant] · LFs s a₀ j₀`.
* **The decomposition data** `decompData` and **`decompStmt : DecompStmt`** (without hypotheses).
-/
import CollatzProof.Arctic.Nat.W3DecompProof7

namespace Collatz.Arctic.NatQ5.W3c

open Collatz.Arctic Collatz.Arctic.NatQ5 Matrix
open Collatz.Arctic.MinIdeal (BRel)

set_option linter.unusedSectionVars false

attribute [local instance] fintypeBRelZ

section Words2

theorem take_block (α β u : List (Fin 2)) {R k : ℕ} (hk : k ≤ R) :
    (α ++ (List.replicate R u).flatten ++ β).take (α.length + k * u.length) = α ++ (List.replicate k u).flatten := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [List.replicate_add, List.flatten_append, List.append_assoc, List.append_assoc, List.take_append,
    List.take_of_length_le (by omega), List.take_append]
  have hl : ((List.replicate k u).flatten).length = k * u.length := by
    simp [List.length_flatten, List.map_replicate, List.sum_replicate]
  rw [hl, List.take_of_length_le (by omega), show α.length + k * u.length - α.length - k * u.length = 0 by omega,
    List.take_zero, List.append_nil]

variable (u τ' y'' z m : List (Fin 2)) (R : ℕ)

theorem length_fullW' : (fullW u τ' y'' z m R).length =
    (topW u τ' R).length + m.length + (y''.length + R * u.length + z.length) := by
  rw [length_fullW, length_tailW]

theorem copy_top {c0 : ℕ} (hc : c0 < R) :
    seg (fullW u τ' y'' z m R) (τ'.length + c0 * u.length) (τ'.length + c0 * u.length + u.length) = u := by
  rw [fullW_assoc_top]; exact copy_seg τ' _ u hc

theorem copy_tail {c1 : ℕ} (hc : c1 < R) :
    seg (fullW u τ' y'' z m R) ((topW u τ' R).length + m.length + (y''.length + c1 * u.length))
      ((topW u τ' R).length + m.length + (y''.length + c1 * u.length) + u.length) = u := by
  rw [fullW_assoc_tail]
  have := copy_seg (topW u τ' R ++ m ++ y'') z u hc
  simp only [List.length_append] at this
  rw [show (topW u τ' R).length + m.length + (y''.length + c1 * u.length) =
    (topW u τ' R).length + m.length + y''.length + c1 * u.length by omega]
  exact this

end Words2

section Final

variable {Q : Type} [Fintype Q] [DecidableEq Q] {A : ValAuto Q} {u : List (Fin 2)} {K : Set (BRel (ZIdx A))}
  {e : BRel (ZIdx A)}

/-- Terms with indices that are not relevant vanish. -/
theorem rel_of_uv_mid_wv {τ' y'' z : List (Fin 2)} {R c0 c1 : ℕ} {j0 j1 : Q} {M : Matrix Q Q ℕ}
    (hM : ∀ a b, 1 ≤ M a b → Conn A a b)
    (h : Uv A u τ' R c0 j0 * M j0 j1 * Wv A u y'' z R c1 j1 ≠ 0) : Rel A j0 ∧ Rel A j1 := by
  have hU : Uv A u τ' R c0 j0 ≠ 0 := fun h0 => h (by rw [h0]; simp)
  have hMM : M j0 j1 ≠ 0 := fun h0 => h (by rw [h0]; simp)
  have hW : Wv A u y'' z R c1 j1 ≠ 0 := fun h0 => h (by rw [h0]; simp)
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hU
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hW
  have hu : 1 ≤ A.u i := Nat.one_le_iff_ne_zero.2 fun h0 => hi (by rw [h0, zero_mul])
  have hci : Conn A i j0 := conn_of_Umat A u (Nat.one_le_iff_ne_zero.2 fun h0 => hi (by rw [h0, mul_zero]))
  have hv : 1 ≤ A.v j := Nat.one_le_iff_ne_zero.2 fun h0 => hj (by rw [h0, mul_zero])
  have hcj : Conn A j1 j := conn_of_Wmat A u (Nat.one_le_iff_ne_zero.2 fun h0 => hj (by rw [h0, zero_mul]))
  have hc01 : Conn A j0 j1 := hM j0 j1 (Nat.one_le_iff_ne_zero.2 hMM)
  exact ⟨⟨⟨i, hu, hci⟩, ⟨j, conn_trans A hc01 hcj, hv⟩⟩, ⟨⟨i, hu, conn_trans A hci hc01⟩, ⟨j, hcj, hv⟩⟩⟩

theorem conn_of_mid {w : List (Fin 2)} {a b : Q}
    (h : 1 ≤ (Rigid.DxN (Dp A) u * Rigid.DxN A.B w * Rigid.DxN (Dp A) u) a b) : Conn A a b := by
  obtain ⟨c, h1, h2⟩ := exists_mid_mul h
  obtain ⟨d, h3, h4⟩ := exists_mid_mul h1
  exact conn_trans A (conn_trans A (conn_of_DxN A (le_trans h3 (DxN_Dp_le A u a d)))
    (conn_of_DxN A h4)) (conn_of_DxN A (le_trans h2 (DxN_Dp_le A u c b)))

variable (h01 : ∀ C, IsComp A C → ZeroOne A C) (hS : Sharp A K u e)
include hS

/-- `s_T = s_{t₁}`: between `t₁` and `T` there are copies of `u♯`, and `μ = e` is absorbed. -/
theorem sT_eq (τ' y'' z m : List (Fin 2)) {R c1 : ℕ} (hc : c1 < R) :
    muZ A ((fullW u τ' y'' z m R).take (posT u τ' y'' m R)) =
      muZ A ((fullW u τ' y'' z m R).take
        ((topW u τ' R).length + m.length + (y''.length + c1 * u.length) + u.length)) := by
  rw [fullW_assoc_tail]
  have h1 : posT u τ' y'' m R = (topW u τ' R ++ m ++ y'').length + R * u.length := by
    simp only [posT, List.length_append]
  have h2 : (topW u τ' R).length + m.length + (y''.length + c1 * u.length) + u.length =
      (topW u τ' R ++ m ++ y'').length + (c1 + 1) * u.length := by
    simp only [List.length_append]; ring
  rw [h1, h2, take_block _ _ _ le_rfl, take_block _ _ _ (show c1 + 1 ≤ R by omega),
    muZ_append A (topW u τ' R ++ m ++ y'') (List.replicate R u).flatten,
    muZ_append A (topW u τ' R ++ m ++ y'') (List.replicate (c1 + 1) u).flatten,
    hS.mu_pow A (by omega), hS.mu_pow A (by omega)]

include h01

/-- **Agreement for each skeleton**: `termOf(γ) = Uv · Wv · [relevant] · LFs s a₀ j₀`. -/
theorem term_gamma (τ' y'' z m : List (Fin 2)) {R : ℕ} {c0 c1 : ℕ} (hc0 : c0 < R) (hc1 : c1 < R) (j0 j1 : Q) (s : ℕ) :
    termOf A Prod.fst s
        (fun sT l => Uv A u τ' R c0 j0 * Wv A u y'' z R c1 j1 * ind (Rel A j0 ∧ Rel A j1) *
          thetaChain A e sT j1 s (muZ A ((topW u τ' R).take (τ'.length + c0 * u.length))) e j0 l)
        (fun _ => gfun A u) (τ'.length + c0 * u.length + u.length)
        ((topW u τ' R).length + m.length + (y''.length + c1 * u.length + u.length))
        (muZ A ((fullW u τ' y'' z m R).take (posT u τ' y'' m R))) (fullW u τ' y'' z m R) =
      Uv A u τ' R c0 j0 * Wv A u y'' z R c1 j1 * ind (Rel A j0 ∧ Rel A j1) *
        LFs A u (fullW u τ' y'' z m R) ((topW u τ' R).length + m.length + (y''.length + c1 * u.length)) j1 s
          (τ'.length + c0 * u.length) j0 := by
  set ω := fullW u τ' y'' z m R
  set a0 := τ'.length + c0 * u.length
  set tm := (topW u τ' R).length + m.length + (y''.length + c1 * u.length)
  have hcopy : seg ω tm (tm + u.length) = u := copy_tail u τ' y'' z m R hc1
  have hN : tm + u.length ≤ ω.length := by
    rw [length_fullW']
    have : (c1 + 1) * u.length ≤ R * u.length := Nat.mul_le_mul_right _ (by omega)
    simp only [tm]; nlinarith
  have hcopy0 : seg ω a0 (a0 + u.length) = u := copy_top u τ' y'' z m R hc0
  have hlt := length_topW u τ' R
  have ha0top : a0 + u.length ≤ (topW u τ' R).length := by
    have : (c0 + 1) * u.length ≤ R * u.length := Nat.mul_le_mul_right _ (by omega)
    rw [hlt]; simp only [a0]; nlinarith
  have ha0tm : a0 ≤ tm := by simp only [tm]; omega
  -- `firstOcc a₀ = a₀`
  have hocc0 : occAt u ω a0 := ⟨by omega, by
    have : seg ω a0 (a0 + u.length) = (ω.drop a0).take u.length := by simp [seg]
    rw [← this, hcopy0]⟩
  have hfo : firstOcc u ω a0 = a0 :=
    le_antisymm (firstOcc_le le_rfl hocc0) (firstOcc_spec ⟨a0, le_rfl, hocc0⟩).1
  -- take out the constants
  have hconst : termOf A Prod.fst s
        (fun sT l => Uv A u τ' R c0 j0 * Wv A u y'' z R c1 j1 * ind (Rel A j0 ∧ Rel A j1) *
          thetaChain A e sT j1 s (muZ A ((topW u τ' R).take a0)) e j0 l)
        (fun _ => gfun A u) (a0 + u.length)
        ((topW u τ' R).length + m.length + (y''.length + c1 * u.length + u.length))
        (muZ A (ω.take (posT u τ' y'' m R))) ω =
      Uv A u τ' R c0 j0 * Wv A u y'' z R c1 j1 * ind (Rel A j0 ∧ Rel A j1) *
        frz A u e ω (tm + u.length) (muZ A (ω.take (tm + u.length))) j1 s (a0 + u.length)
          (muZ A ((topW u τ' R).take a0)) e j0 := by
    unfold frz termOf
    rw [Finset.mul_sum, show (topW u τ' R).length + m.length + (y''.length + c1 * u.length + u.length) =
      tm + u.length by simp only [tm]; omega, sT_eq hS τ' y'' z m hc1]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hconst]
  -- bring the start into the form of `frz_eq`
  have hσ : muZ A ((topW u τ' R).take a0) = muZ A (ω.take a0) := by
    rw [take_fullW_top u τ' y'' z m R (by omega)]
  have he : e = muZ A (seg ω a0 (firstOcc u ω a0 + u.length)) := by rw [hfo, hcopy0, hS.mu_eq]
  have ht0 : a0 + u.length = firstOcc u ω a0 + u.length := by rw [hfo]
  have hfe := frz_eq (j1 := j1) h01 hS hcopy hN s a0 j0 ha0tm
  rw [← he, ← ht0, ← hσ] at hfe
  rw [hfe]

/-- **The main identity** (the contents of `DecompData.spec`). -/
theorem spec_core {R : ℕ} (hR : Fintype.card Q ≤ R) (τ' y'' z m : List (Fin 2)) :
    aval A (fullW u τ' y'' z m R) =
      ∑ γ : Fin R × Q × Fin R × Q × Fin (Fintype.card Q),
        termOf A Prod.fst γ.2.2.2.2.val
          (fun sT l => Uv A u τ' R γ.1.val γ.2.1 * Wv A u y'' z R γ.2.2.1.val γ.2.2.2.1 *
            ind (Rel A γ.2.1 ∧ Rel A γ.2.2.2.1) *
            thetaChain A e sT γ.2.2.2.1 γ.2.2.2.2.val (muZ A ((topW u τ' R).take (τ'.length + γ.1.val * u.length)))
              e γ.2.1 l)
          (fun _ => gfun A u) (τ'.length + γ.1.val * u.length + u.length)
          ((topW u τ' R).length + m.length + (y''.length + γ.2.2.1.val * u.length + u.length))
          (muZ A ((fullW u τ' y'' z m R).take (posT u τ' y'' m R))) (fullW u τ' y'' z m R) := by
  rw [aval_blocks hS hR τ' y'' z m]
  simp only [Fintype.sum_prod_type]
  -- agreement for each skeleton
  rw [Finset.sum_congr rfl fun c0 _ => Finset.sum_congr rfl fun j0 _ => Finset.sum_congr rfl fun c1 _ =>
    Finset.sum_congr rfl fun j1 _ => Finset.sum_congr rfl fun s _ =>
      term_gamma h01 hS τ' y'' z m c0.isLt c1.isLt j0 j1 s.val]
  -- the sum over `s` is `LFp`, and then the middle factor
  have hmid : ∀ (c0 c1 : ℕ), c0 < R → c1 < R → ∀ j0 j1 : Q,
      ∑ s : Fin (Fintype.card Q), Uv A u τ' R c0 j0 * Wv A u y'' z R c1 j1 * ind (Rel A j0 ∧ Rel A j1) *
        LFs A u (fullW u τ' y'' z m R) ((topW u τ' R).length + m.length + (y''.length + c1 * u.length)) j1 s.val
          (τ'.length + c0 * u.length) j0 =
      Uv A u τ' R c0 j0 * Wv A u y'' z R c1 j1 * ind (Rel A j0 ∧ Rel A j1) *
        (Rigid.DxN (Dp A) u * Rigid.DxN A.B (seg (fullW u τ' y'' z m R) (τ'.length + c0 * u.length + u.length)
          ((topW u τ' R).length + m.length + (y''.length + c1 * u.length))) * Rigid.DxN (Dp A) u) j0 j1 := by
    intro c0 c1 hc0 hc1 j0 j1
    rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun s => LFs A u (fullW u τ' y'' z m R)
      ((topW u τ' R).length + m.length + (y''.length + c1 * u.length)) j1 s (τ'.length + c0 * u.length) j0)]
    by_cases hr : Rel A j0 ∧ Rel A j1
    · set ω := fullW u τ' y'' z m R
      set a0 := τ'.length + c0 * u.length
      set tm := (topW u τ' R).length + m.length + (y''.length + c1 * u.length)
      have hcopy : seg ω tm (tm + u.length) = u := copy_tail u τ' y'' z m R hc1
      have hN : tm + u.length ≤ ω.length := by
        rw [length_fullW']
        have : (c1 + 1) * u.length ≤ R * u.length := Nat.mul_le_mul_right _ (by omega)
        simp only [tm]; nlinarith
      have hcopy0 : seg ω a0 (a0 + u.length) = u := copy_top u τ' y'' z m R hc0
      have hlt := length_topW u τ' R
      have ha0top : a0 + u.length ≤ (topW u τ' R).length := by
        have : (c0 + 1) * u.length ≤ R * u.length := Nat.mul_le_mul_right _ (by omega)
        rw [hlt]; simp only [a0]; nlinarith
      have ha0tm : a0 + u.length ≤ tm := by simp only [tm]; omega
      rw [← LFp_flat h01 hS hcopy hN hr.2 a0 (by omega) j0 hr.1, ← mid_eq_LFp h01 hS hcopy hN hcopy0 ha0tm hr.1]
    · rw [ind_neg hr]; simp
  rw [Finset.sum_congr rfl fun c0 _ => Finset.sum_congr rfl fun j0 _ => Finset.sum_congr rfl fun c1 _ =>
    Finset.sum_congr rfl fun j1 _ => hmid c0.val c1.val c0.isLt c1.isLt j0 j1]
  -- the sum over `Fin R` as a sum over `range R`
  rw [Fin.sum_univ_eq_sum_range (fun c0 => ∑ j0, ∑ c1 : Fin R, ∑ j1,
    Uv A u τ' R c0 j0 * Wv A u y'' z R c1.val j1 * ind (Rel A j0 ∧ Rel A j1) *
      (Rigid.DxN (Dp A) u * Rigid.DxN A.B (seg (fullW u τ' y'' z m R) (τ'.length + c0 * u.length + u.length)
        ((topW u τ' R).length + m.length + (y''.length + c1.val * u.length))) * Rigid.DxN (Dp A) u) j0 j1) R]
  refine Finset.sum_congr rfl fun c0 _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  rw [Fin.sum_univ_eq_sum_range (fun c1 => ∑ j0, ∑ j1,
    Uv A u τ' R c0 j0 * Wv A u y'' z R c1 j1 * ind (Rel A j0 ∧ Rel A j1) *
      (Rigid.DxN (Dp A) u * Rigid.DxN A.B (seg (fullW u τ' y'' z m R) (τ'.length + c0 * u.length + u.length)
        ((topW u τ' R).length + m.length + (y''.length + c1 * u.length))) * Rigid.DxN (Dp A) u) j0 j1) R]
  refine Finset.sum_congr rfl fun c1 _ => Finset.sum_congr rfl fun j0 _ => Finset.sum_congr rfl fun j1 _ => ?_
  -- terms with indices that are not relevant vanish
  by_cases hr : Rel A j0 ∧ Rel A j1
  · rw [ind_pos hr]; ring
  · rw [ind_neg hr, mul_zero, zero_mul]
    by_contra hne
    exact hr (rel_of_uv_mid_wv (fun a b h => conn_of_mid h) hne)

/-- **The decomposition data** (Proposition 12.11). -/
noncomputable def decompData {R : ℕ} (hR : Fintype.card Q ≤ R) (τ' y'' z : List (Fin 2)) :
    DecompData A u τ' y'' z R where
  Γ := Fin R × Q × Fin R × Q × Fin (Fintype.card Q)
  finΓ := inferInstance
  deg γ := γ.2.2.2.2.val
  t0 γ := τ'.length + γ.1.val * u.length + u.length
  t1 γ := y''.length + γ.2.2.1.val * u.length + u.length
  t0_le γ := by
    have : (γ.1.val + 1) * u.length ≤ R * u.length := Nat.mul_le_mul_right _ γ.1.isLt
    rw [length_topW]; nlinarith
  t1_le γ := by
    have : (γ.2.2.1.val + 1) * u.length ≤ R * u.length := Nat.mul_le_mul_right _ γ.2.2.1.isLt
    nlinarith
  Lab := LabT A
  finLab := inferInstance
  labS := Prod.fst
  κ γ sT l := Uv A u τ' R γ.1.val γ.2.1 * Wv A u y'' z R γ.2.2.1.val γ.2.2.2.1 *
    ind (Rel A γ.2.1 ∧ Rel A γ.2.2.2.1) *
    thetaChain A e sT γ.2.2.2.1 γ.2.2.2.2.val (muZ A ((topW u τ' R).take (τ'.length + γ.1.val * u.length)))
      e γ.2.1 l
  g _ _ l r v := gfun A u l r v
  g_len _ _ l r v h := gfun_len A u l r v h
  cP := (Fintype.card Q ^ 2 * Wmax A + 1) ^ Fintype.card Q
  dP := Fintype.card Q + 1
  g_poly _ _ l r v := gfun_poly h01 l r v
  cW := Fintype.card Q + 2
  g_free _ _ l r v h := gfun_free h01 hS l r v h
  spec m := spec_core h01 hS hR τ' y'' z m

end Final

/-- **The target `DecompStmt` holds without hypotheses** (Proposition 12.11). -/
theorem decompStmt : DecompStmt := by
  intro Q _ _ A h01 K u e hS R hR τ' y'' z
  exact ⟨decompData h01 hS hR τ' y'' z⟩

end Collatz.Arctic.NatQ5.W3c
