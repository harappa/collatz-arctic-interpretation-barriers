/-
# Lemma 11.3: a component with a uniform lower bound exists (without Kingman)

Instead of an earlier argument (Lyapunov exponents of the components by Kingman's subadditive ergodic theorem,
and rigidity of the top component), we show by contradiction
"**some strongly connected component has a uniform lower bound `‖D^S_x‖ ≥ c G^{|x|}`**" and turn this into `RigidAt` by
`rigidAt_iff_uniform_lower` of Appendix D (`top_rigid`; Lemma 11.3). This answers in Lean a question raised when planning the formalization.

**Hypotheses**: `1 < G`, the diagonal bound `(B_w)_{ii} ≤ G^{|w|}` for all words and indices, and for all `κ ≥ 1`
`κ log G ≤ bAvg_κ := 2^{-κ} Σ_{|x|=κ} log⁺ ‖B_x‖` (the form of the conclusion of Theorem 11.8).

**Proof**: suppose that no component `S` has a uniform lower bound.
1. For each component, `φ_S(x) := ‖E^S_x‖ = G^{-|x|} ‖D^S_x‖` is submultiplicative and at most `C_S` (Lemma D.2, `Ex_entry_bound`). As there is no uniform
   lower bound, there is a word `y_S` with `φ_S(y_S) < 1/(2 C_S^3)`.
2. Concatenating the words `y_S` over all components gives `z₀`, and `C_S φ_S(z₀) ≤ C_S · C_S φ_S(y_S) C_S < 1/2` for every `S`.
   Take a power `z` of `z₀` with `G^{|z|} ≥ 2` (still `C_S φ_S(z) < 1/2`).
3. `κ := |z|`, `θ := 1/2`. By `phi_blocks_le` of Appendix D, `(D^S_{bs})_{xy} ≤ C G^{|bs|} θ^{#z(bs)}` on each component.
   By `path_block_bound` (Lemma 11.1), `‖B_{bs}‖ ≤ K (m + 1)^{|Q|} G^{mκ} θ^{#z(bs)}` on the whole automaton.
4. Average `log⁺`: the average of the number of segments `#z(bs)` is `m 2^{-κ}` (`bsum_affine_count`, only the linearity of expectation), so
   `bAvg_{mκ} ≤ log K + |Q| log(m + 1) + mκ log G - m 2^{-κ} log 2`. Together with the hypothesis `mκ log G ≤ bAvg_{mκ}`,
   `m 2^{-κ} log 2 ≤ log K + |Q| log(m + 1)` holds for all `m ≥ 1`, which contradicts the fact that `log` grows more slowly than linear functions.

Kingman, Fekete, the existence of limits, Perron–Frobenius and concentration estimates are not used. Nor is the case distinction "top" / "not top" of an earlier argument needed
(we do not show that the component of the conclusion is a top component (`g_S = G`); downstream, `heavy_family` needs only `RigidAt _ G`).

**The form with a weakened hypothesis** (`top_rigid_of_liminf`): instead of `∀ κ ≥ 1, κ log G ≤ bAvg_κ`,
`liminf_κ bAvg_κ / κ ≥ log G` (for every `ε > 0` there is `N` with `κ log G ≤ bAvg_κ + εκ` for `κ ≥ N`) suffices,
since the proof only uses `κ = m|z|` (with `m` large). `top_rigid` is a corollary.

**Passing downstream**: `top_rigid'` (strong connectivity, rigidity, the uniform lower bound and an internal edge, bundled), and `top_heavy` (through
`heavy_family` of Appendix D, in the form `(B_{ω_ε})_{aa} ≥ c G^{|ω_ε|}` for the entries of the whole automaton; Corollary 11.4).
-/
import CollatzProof.Arctic.Nat.H2Path
import CollatzProof.Arctic.Nat.RigidLower
import CollatzProof.Arctic.Nat.RigidSep

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Matrix Filter Topology

set_option linter.unusedSectionVars false

namespace W2b

/-! ## §1 Linear growth is not bounded by a logarithm -/

/-- `m c ≤ a + p log(m + 1)` (`c > 0`) fails for all sufficiently large `m` (`m ≥ M₀`). -/
theorem not_linear_le_log {c a : ℝ} (p M₀ : ℕ) (hc : 0 < c)
    (h : ∀ m : ℕ, M₀ ≤ m → (m : ℝ) * c ≤ a + p * Real.log ((m : ℝ) + 1)) : False := by
  set ε : ℝ := c / (2 * ((p : ℝ) + 1)) with hε
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hε0 : 0 < ε := div_pos hc (by linarith)
  have hpε : (p : ℝ) * ε ≤ c / 2 := by
    rw [hε, mul_div_assoc', div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 (Real.isLittleO_log_id_atTop.def hε0)
  obtain ⟨m, hm⟩ := exists_nat_gt (max (max N₀ (2 * |a| / c + 2)) (M₀ : ℝ))
  have hm' : max N₀ (2 * |a| / c + 2) < (m : ℝ) := lt_of_le_of_lt (le_max_left _ _) hm
  have hmN : N₀ ≤ (m : ℝ) + 1 := by linarith [le_max_left N₀ (2 * |a| / c + 2)]
  have hmA : 2 * |a| / c + 2 < (m : ℝ) := lt_of_le_of_lt (le_max_right _ _) hm'
  have hm1 : M₀ ≤ m := by
    have : (M₀ : ℝ) < m := lt_of_le_of_lt (le_max_right _ _) hm
    exact_mod_cast this.le
  have hlog : Real.log ((m : ℝ) + 1) ≤ ε * ((m : ℝ) + 1) := by
    have h1 := hN₀ ((m : ℝ) + 1) hmN
    rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos (show (0 : ℝ) < (m : ℝ) + 1 by positivity)] at h1
    exact (le_abs_self _).trans h1
  have h2 := h m hm1
  have h3 : (p : ℝ) * Real.log ((m : ℝ) + 1) ≤ c / 2 * ((m : ℝ) + 1) := by
    calc (p : ℝ) * Real.log ((m : ℝ) + 1) ≤ p * (ε * ((m : ℝ) + 1)) := mul_le_mul_of_nonneg_left hlog hp0
      _ = (p * ε) * ((m : ℝ) + 1) := by ring
      _ ≤ c / 2 * ((m : ℝ) + 1) := mul_le_mul_of_nonneg_right hpε (by positivity)
  have h4 : c * (2 * |a| / c + 2) < c * m := mul_lt_mul_of_pos_left hmA hc
  have h5 : c * (2 * |a| / c + 2) = 2 * |a| + 2 * c := by field_simp
  have h6 : a ≤ |a| := le_abs_self a
  nlinarith

/-! ## §2 `φ_S(x) := ‖E^S_x‖` for each component -/

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- `φ(x) := ‖G^{-|x|} D^S_x‖` of the component `sccOf A q`. -/
noncomputable def phiC (A : ValAuto Q) (G : ℝ) (q : Q) (x : List (Fin 2)) : ℝ :=
  Rigid.nrm (Rigid.Ex (compMat A (sccOf A q)) G x)

theorem phiC_nonneg (A : ValAuto Q) (G : ℝ) (q : Q) (x : List (Fin 2)) : 0 ≤ phiC A G q x :=
  Rigid.nrm_nonneg _

theorem phiC_mul (A : ValAuto Q) (G : ℝ) (q : Q) (x y : List (Fin 2)) :
    phiC A G q (x ++ y) ≤ phiC A G q x * phiC A G q y := by
  unfold phiC
  rw [Rigid.Ex_append]
  exact Rigid.nrm_mul_le _ _

theorem nrm_Dx_comp_eq (A : ValAuto Q) {G : ℝ} (hG0 : 0 < G) (q : Q) (x : List (Fin 2)) :
    Rigid.nrm (Rigid.Dx (compMat A (sccOf A q)) x) = G ^ x.length * phiC A G q x :=
  Rigid.nrm_Dx_eq _ G hG0 x

/-- `φ_S` is bounded (Lemma D.2). -/
theorem phiC_le (A : ValAuto Q) {G : ℝ} (hG : 1 ≤ G)
    (hdiag : ∀ (w : List (Fin 2)) (i : Q), Rigid.Dx A.B w i i ≤ G ^ w.length) (q : Q) :
    ∃ Cq : ℝ, 1 ≤ Cq ∧ ∀ x, phiC A G q x ≤ Cq := by
  have hG0 : 0 < G := by linarith
  obtain ⟨L, hL⟩ := Rigid.Ex_entry_bound _ (sc_compMat A q) hG (diag_compMat A hdiag q)
  refine ⟨max 1 ((Fintype.card (sccOf A q) : ℝ) ^ 2 * G ^ L), le_max_left _ _, fun x => ?_⟩
  refine (Rigid.nrm_le_of_entry_le fun i j => ?_).trans (le_max_right _ _)
  rw [abs_of_nonneg (Rigid.Ex_nonneg _ hG0.le x i j)]
  exact hL x i j

/-- On a component without a uniform lower bound, `φ_S` takes arbitrarily small values on words. -/
theorem phiC_small (A : ValAuto Q) {G : ℝ} (hG : 1 < G)
    (hdiag : ∀ (w : List (Fin 2)) (i : Q), Rigid.Dx A.B w i i ≤ G ^ w.length) (q : Q)
    (hno : ¬ Rigid.RigidAt (compMat A (sccOf A q)) G) : ∀ c : ℝ, 0 < c → ∃ x, phiC A G q x < c := by
  have hG0 : 0 < G := by linarith
  rw [Rigid.rigidAt_iff_uniform_lower _ (sc_compMat A q) hG (diag_compMat A hdiag q)] at hno
  push Not at hno
  intro c hc
  obtain ⟨x, hx⟩ := hno c hc
  refine ⟨x, ?_⟩
  rw [nrm_Dx_comp_eq A hG0 q x, mul_comm c] at hx
  exact lt_of_mul_lt_mul_left hx (pow_nonneg hG0.le _)

/-! ## §3 The pointwise bound for `log⁺` on sequences of segments -/

/-- The `log` of `X := K (m + 1)^p (G^{mκ} θ^{c})` (`θ = 1/2`). -/
theorem log_bound_eq {K G : ℝ} (hK : 0 < K) (hG0 : 0 < G) (m p n c : ℕ) :
    Real.log (K * ((m : ℝ) + 1) ^ p * (G ^ n * (1 / 2 : ℝ) ^ c)) =
      Real.log K + p * Real.log ((m : ℝ) + 1) + n * Real.log G + Real.log (1 / 2) * c := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  rw [Real.log_mul (mul_pos hK (pow_pos hm _)).ne' (mul_pos (pow_pos hG0 _) (by positivity)).ne',
    Real.log_mul hK.ne' (pow_pos hm _).ne', Real.log_mul (pow_pos hG0 _).ne' (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow]
  ring

end W2b

/-! ## §4 The main theorem -/

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

open W2b in
/-- **Lemma 11.3 with the weak hypothesis, `top_rigid_of_liminf`**: if `1 < G`, `(B_w)_{ii} ≤ G^{|w|}` for all words and indices, and
`liminf_κ bAvg_κ / κ ≥ log G` (for every `ε > 0` there is `N` with `κ log G ≤ bAvg_κ + εκ` for `κ ≥ N`), then
**some strongly connected component `sccOf A q` is rigid at `G`**. -/
theorem top_rigid_of_liminf (A : ValAuto Q) {G : ℝ} (hG : 1 < G)
    (hdiag : ∀ (w : List (Fin 2)) (i : Q), Rigid.Dx A.B w i i ≤ G ^ w.length)
    (hLC : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ κ : ℕ, N ≤ κ → (κ : ℝ) * Real.log G ≤ Rigid.bAvg A.B κ + ε * κ) :
    ∃ q, Rigid.RigidAt (compMat A (sccOf A q)) G := by
  by_contra hno
  push Not at hno
  have hG0 : 0 < G := by linarith
  have hlogG : 0 < Real.log G := Real.log_pos hG
  -- (0) The index type is non-empty
  have hne : Nonempty Q := by
    by_contra hQ
    rw [not_nonempty_iff] at hQ
    obtain ⟨N, hN⟩ := hLC (Real.log G / 2) (by linarith)
    have h1 := hN (N + 1) (by omega)
    have h0 : Rigid.bAvg A.B (N + 1) = 0 := by
      unfold Rigid.bAvg
      have hz : ∀ Y : Matrix Q Q ℝ, Rigid.nrm Y = 0 := fun Y => by
        have := hQ; simp [Rigid.nrm]
      simp [hz]
    rw [h0] at h1
    have hN1 : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  obtain ⟨q₀⟩ := hne
  -- (1) Upper bounds and small words for each component
  choose Cq hCq1 hCq using fun q => phiC_le A hG.le hdiag q
  have hCq0 : ∀ q, 0 < Cq q := fun q => lt_of_lt_of_le one_pos (hCq1 q)
  choose y hy using fun q => phiC_small A hG hdiag q (hno q) (1 / (2 * Cq q ^ 3))
    (by have := hCq0 q; positivity)
  -- (2) A word `z₀` common to all components
  set z₀ : List (Fin 2) := ((Finset.univ : Finset Q).toList.map y).flatten with hz₀
  have hz₀q : ∀ q, Cq q * phiC A G q z₀ < 1 / 2 := by
    intro q
    obtain ⟨s, t, hst⟩ := List.append_of_mem
      (List.mem_map_of_mem (f := y) (Finset.mem_toList.2 (Finset.mem_univ q)))
    have e : z₀ = s.flatten ++ (y q ++ t.flatten) := by
      rw [hz₀, hst, List.flatten_append, List.flatten_cons]
    rw [e]
    have hC := hCq1 q
    have hC0 := hCq0 q
    have h1 : phiC A G q (s.flatten ++ (y q ++ t.flatten)) ≤ Cq q * (phiC A G q (y q) * Cq q) := by
      refine (phiC_mul A G q _ _).trans ?_
      refine mul_le_mul (hCq q _) ((phiC_mul A G q _ _).trans
        (mul_le_mul_of_nonneg_left (hCq q _) (phiC_nonneg A G q _)))
        (phiC_nonneg A G q _) hC0.le
    have hC3 : (0 : ℝ) < Cq q ^ 3 := pow_pos hC0 3
    calc Cq q * phiC A G q (s.flatten ++ (y q ++ t.flatten))
        ≤ Cq q * (Cq q * (phiC A G q (y q) * Cq q)) := mul_le_mul_of_nonneg_left h1 hC0.le
      _ = Cq q ^ 3 * phiC A G q (y q) := by ring
      _ < Cq q ^ 3 * (1 / (2 * Cq q ^ 3)) := mul_lt_mul_of_pos_left (hy q) hC3
      _ = 1 / 2 := by field_simp
  have hz₀ne : z₀ ≠ [] := by
    intro h
    have h1 := hz₀q q₀
    rw [h] at h1
    have hp : phiC A G q₀ [] = ((sccOf A q₀).card : ℝ) := by
      unfold phiC
      rw [Rigid.Ex_nil, Rigid.nrm_one, Fintype.card_coe]
    have hcard : (1 : ℝ) ≤ (sccOf A q₀).card := by
      exact_mod_cast Finset.card_pos.2 ⟨q₀, self_mem_sccOf A q₀⟩
    rw [hp] at h1
    nlinarith [hCq1 q₀]
  -- (3) A power `z` of `z₀` (`G^{|z|} ≥ 2`)
  have hgl : 1 < G ^ z₀.length :=
    one_lt_pow₀ hG (by simpa [List.length_eq_zero_iff] using hz₀ne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 : ℝ) hgl
  have hn0 : n ≠ 0 := by rintro rfl; norm_num at hn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  set z : List (Fin 2) := Rigid.rep z₀ (j + 1) with hzdef
  set κ : ℕ := z.length with hκdef
  have hκ : κ = (j + 1) * z₀.length := Rigid.rep_length z₀ _
  have hκpos : 0 < κ := by
    rw [hκ]; exact Nat.mul_pos (Nat.succ_pos _) (List.length_pos_iff.mpr hz₀ne)
  have hGκ : 2 ≤ G ^ κ := by
    rw [hκ, mul_comm, pow_mul]; exact hn.le
  have hzq : ∀ q, Cq q * phiC A G q z ≤ 1 / 2 := by
    intro q
    have hφ1 : phiC A G q z₀ ≤ 1 := by
      nlinarith [hz₀q q, hCq1 q, phiC_nonneg A G q z₀]
    have h1 : phiC A G q z ≤ phiC A G q z₀ :=
      (Rigid.phi_rep_le (phiC_nonneg A G q) (phiC_mul A G q) z₀ j).trans
        (pow_le_of_le_one (phiC_nonneg A G q z₀) hφ1 (Nat.succ_ne_zero _))
    calc Cq q * phiC A G q z ≤ Cq q * phiC A G q z₀ := mul_le_mul_of_nonneg_left h1 (hCq0 q).le
      _ ≤ 1 / 2 := (hz₀q q).le
  -- (4) The bound over segments on each component (`θ = 1/2`, with the uniform constant `Cm`)
  obtain ⟨Cm, hCm⟩ := (Set.finite_range Cq).bddAbove
  have hCm' : ∀ q, Cq q ≤ Cm := fun q => hCm ⟨q, rfl⟩
  have hS : ∀ q (bs : List (List (Fin 2))), (∀ b ∈ bs, b.length = κ) → ∀ x y : sccOf A q,
      (DC A (sccOf A q) bs.flatten x y : ℝ) ≤ Cm * G ^ bs.flatten.length * (1 / 2 : ℝ) ^ bs.count z := by
    intro q bs _ x y
    have hb := Rigid.phi_blocks_le (φ := phiC A G q) (phiC_nonneg A G q) (phiC_mul A G q) (hCq q)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (hzq q) bs []
    rw [List.nil_append] at hb
    have e1 : (DC A (sccOf A q) bs.flatten x y : ℝ) = Rigid.Dx (compMat A (sccOf A q)) bs.flatten x y :=
      (Rigid.Dx_apply _ _ _ _).symm
    have hX : 0 ≤ G ^ bs.flatten.length * (1 / 2 : ℝ) ^ bs.count z :=
      mul_nonneg (pow_nonneg hG0.le _) (pow_nonneg (by norm_num) _)
    rw [e1]
    calc Rigid.Dx (compMat A (sccOf A q)) bs.flatten x y
        ≤ Rigid.nrm (Rigid.Dx (compMat A (sccOf A q)) bs.flatten) := Rigid.le_nrm _ x y
      _ = G ^ bs.flatten.length * phiC A G q bs.flatten := nrm_Dx_comp_eq A hG0 q _
      _ ≤ G ^ bs.flatten.length * (Cq q * (1 / 2) ^ bs.count z) :=
          mul_le_mul_of_nonneg_left hb (pow_nonneg hG0.le _)
      _ = Cq q * (G ^ bs.flatten.length * (1 / 2 : ℝ) ^ bs.count z) := by ring
      _ ≤ Cm * (G ^ bs.flatten.length * (1 / 2 : ℝ) ^ bs.count z) := mul_le_mul_of_nonneg_right (hCm' q) hX
      _ = Cm * G ^ bs.flatten.length * (1 / 2) ^ bs.count z := by ring
  -- (5) The bound on the whole automaton (Lemma 11.1)
  obtain ⟨C', hC'0, hpb⟩ := path_block_bound A (κ := κ) (z := z) (θ := 1 / 2) (C := Cm) hG.le
    (by norm_num) (by norm_num) hS
  set p : ℕ := Fintype.card Q with hp
  set K : ℝ := (p : ℝ) ^ 2 * (2 ^ p * C') + 1 with hK
  have hK1 : 1 ≤ K := by
    have : 0 ≤ (p : ℝ) ^ 2 * (2 ^ p * C') := mul_nonneg (by positivity) (mul_nonneg (by positivity) hC'0)
    linarith
  have hK0 : 0 < K := by linarith
  -- (6) The bound for `log⁺` for each sequence of segments
  have hpt : ∀ (m : ℕ) (bs : List (List (Fin 2))), Rigid.Valid κ m bs →
      Real.posLog (Rigid.nrm (Rigid.Dx A.B bs.flatten)) ≤
        (Real.log K + p * Real.log ((m : ℝ) + 1) + ((m * κ : ℕ) : ℝ) * Real.log G) +
          Real.log (1 / 2) * (bs.count z : ℝ) := by
    intro m bs hbs
    have hlen : bs.flatten.length = m * κ := hbs.flatten_length
    have hbl : bs.length = m := hbs.1
    have hcnt : bs.count z ≤ m := hbl ▸ List.count_le_length
    set M : ℝ := ((m : ℝ) + 1) ^ p * (G ^ (m * κ) * (1 / 2 : ℝ) ^ bs.count z) with hM
    have hM0 : 0 ≤ M := mul_nonneg (by positivity) (mul_nonneg (pow_nonneg hG0.le _) (by positivity))
    have hentry : ∀ i j, |Rigid.Dx A.B bs.flatten i j| ≤ 2 ^ p * (C' * M) := by
      intro i j
      rw [abs_of_nonneg (Rigid.Dx_nonneg _ _ _ _)]
      have h := hpb bs hbs.2 i j
      rw [← Rigid.Dx_apply, hbl, hlen] at h
      have e2 : (2 : ℝ) ^ p * (1 / 2) ^ p = 1 := by rw [← mul_pow]; norm_num
      calc Rigid.Dx A.B bs.flatten i j = (2 ^ p * (1 / 2) ^ p) * Rigid.Dx A.B bs.flatten i j := by
            rw [e2, one_mul]
        _ = 2 ^ p * ((1 / 2) ^ p * Rigid.Dx A.B bs.flatten i j) := by ring
        _ ≤ 2 ^ p * (C' * ((m : ℝ) + 1) ^ p * G ^ (m * κ) * (1 / 2) ^ bs.count z) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = 2 ^ p * (C' * M) := by rw [hM]; ring
    have hnrm : Rigid.nrm (Rigid.Dx A.B bs.flatten) ≤ K * ((m : ℝ) + 1) ^ p * (G ^ (m * κ) * (1 / 2 : ℝ) ^ bs.count z) := by
      refine (Rigid.nrm_le_of_entry_le hentry).trans ?_
      have e3 : K * ((m : ℝ) + 1) ^ p * (G ^ (m * κ) * (1 / 2 : ℝ) ^ bs.count z) = K * M := by
        rw [hM]; ring
      rw [e3, ← hp]
      have : (p : ℝ) ^ 2 * (2 ^ p * (C' * M)) = ((p : ℝ) ^ 2 * (2 ^ p * C')) * M := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith) hM0
    have hX1 : 1 ≤ K * ((m : ℝ) + 1) ^ p * (G ^ (m * κ) * (1 / 2 : ℝ) ^ bs.count z) := by
      have h1 : 1 ≤ ((m : ℝ) + 1) ^ p := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) m])
      have h2 : 1 ≤ G ^ (m * κ) * (1 / 2 : ℝ) ^ bs.count z := by
        have h3 : (1 / 2 : ℝ) ^ m ≤ (1 / 2) ^ bs.count z :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hcnt
        have h4 : 1 ≤ G ^ (m * κ) * (1 / 2 : ℝ) ^ m := by
          rw [pow_mul', ← mul_pow]
          exact one_le_pow₀ (by linarith)
        exact h4.trans (mul_le_mul_of_nonneg_left h3 (pow_nonneg hG0.le _))
      exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK1 h1) h2
    calc Real.posLog (Rigid.nrm (Rigid.Dx A.B bs.flatten))
        ≤ Real.posLog (K * ((m : ℝ) + 1) ^ p * (G ^ (m * κ) * (1 / 2 : ℝ) ^ bs.count z)) :=
          Real.posLog_le_posLog (by linarith [Rigid.nrm_nonneg (Rigid.Dx A.B bs.flatten)]) hnrm
      _ = Real.log (K * ((m : ℝ) + 1) ^ p * (G ^ (m * κ) * (1 / 2 : ℝ) ^ bs.count z)) :=
          Real.posLog_eq_log (by rw [abs_of_pos (by linarith)]; exact hX1)
      _ = _ := by rw [log_bound_eq hK0 hG0]
  -- (7) Average and compare with the hypothesis `hLC`
  set c₀ : ℝ := Real.log 2 / 2 ^ κ with hc₀
  have hc₀0 : 0 < c₀ := div_pos (Real.log_pos one_lt_two) (by positivity)
  obtain ⟨N, hN⟩ := hLC (c₀ / (2 * κ)) (div_pos hc₀0 (by positivity))
  have havg : ∀ m : ℕ, N ≤ m → (m : ℝ) * (c₀ / 2) ≤ Real.log K + p * Real.log ((m : ℝ) + 1) := by
    intro m hm
    have h1 := hN (m * κ) (le_trans hm (Nat.le_mul_of_pos_right m hκpos))
    have hsum := Rigid.bsum_mono (fun bs hbs => hpt m bs hbs)
    rw [Rigid.bsum_affine_count κ z rfl] at hsum
    rw [Rigid.bAvg_eq_wsum, Rigid.wsum_mul_eq_bsum] at h1
    have h2pos : (0 : ℝ) < 2 ^ (m * κ) := by positivity
    have h2 : (2 ^ (m * κ) : ℝ)⁻¹ * Rigid.bsum κ m (fun bs => Real.posLog (Rigid.nrm (Rigid.Dx A.B bs.flatten))) ≤
        Real.log K + p * Real.log ((m : ℝ) + 1) + ((m * κ : ℕ) : ℝ) * Real.log G +
          Real.log (1 / 2) * m / 2 ^ κ := by
      rw [inv_mul_le_iff₀ h2pos]
      refine hsum.trans (le_of_eq ?_)
      ring
    have h3 := h1.trans (add_le_add h2 le_rfl)
    have hl2 : Real.log (1 / 2) = - Real.log 2 := by rw [one_div, Real.log_inv]
    rw [hl2] at h3
    have hκ0 : (κ : ℝ) ≠ 0 := by exact_mod_cast hκpos.ne'
    have e1 : -Real.log 2 * m / 2 ^ κ = -((m : ℝ) * c₀) := by rw [hc₀]; ring
    have e2 : c₀ / (2 * κ) * ((m * κ : ℕ) : ℝ) = (m : ℝ) * (c₀ / 2) := by
      push_cast; field_simp
    rw [e1, e2] at h3
    have e3 : (m : ℝ) * c₀ = 2 * ((m : ℝ) * (c₀ / 2)) := by ring
    rw [e3] at h3
    linarith
  exact not_linear_le_log p N (c := c₀ / 2) (a := Real.log K) (by linarith) havg

open W2b in
/-- **`top_rigid` (Lemma 11.3, replacing the earlier argument through Kingman's theorem)**: if `1 < G`, `(B_w)_{ii} ≤ G^{|w|}` for all words and indices,
and `κ log G ≤ bAvg_κ` for all `κ ≥ 1`, then **some strongly connected component `sccOf A q` is rigid at `G`**
(`RigidAt`; by `rigidAt_iff_uniform_lower` of Appendix D, equivalent to the uniform lower bound `‖D^S_x‖ ≥ c G^{|x|}`). -/
theorem top_rigid (A : ValAuto Q) {G : ℝ} (hG : 1 < G)
    (hdiag : ∀ (w : List (Fin 2)) (i : Q), Rigid.Dx A.B w i i ≤ G ^ w.length)
    (hLC : ∀ κ : ℕ, 1 ≤ κ → (κ : ℝ) * Real.log G ≤ Rigid.bAvg A.B κ) :
    ∃ q, Rigid.RigidAt (compMat A (sccOf A q)) G := by
  refine top_rigid_of_liminf A hG hdiag fun ε hε => ⟨1, fun κ hκ => ?_⟩
  have := hLC κ hκ
  have : 0 ≤ ε * κ := mul_nonneg hε.le (Nat.cast_nonneg κ)
  linarith

/-- The form of `top_rigid` with the uniform lower bound and the internal edge written out (passed to `heavy_family` and `IsComp` in Proposition 11.13):
for some `q`, the component `sccOf A q` is strongly connected, rigid at `G`, satisfies `‖D^S_x‖ ≥ c G^{|x|}` for all words for some `c > 0`,
and has an internal edge. -/
theorem top_rigid' (A : ValAuto Q) {G : ℝ} (hG : 1 < G)
    (hdiag : ∀ (w : List (Fin 2)) (i : Q), Rigid.Dx A.B w i i ≤ G ^ w.length)
    (hLC : ∀ κ : ℕ, 1 ≤ κ → (κ : ℝ) * Real.log G ≤ Rigid.bAvg A.B κ) :
    ∃ q, Rigid.SC (compMat A (sccOf A q)) ∧ Rigid.RigidAt (compMat A (sccOf A q)) G ∧
      (∃ c : ℝ, 0 < c ∧ ∀ x, c * G ^ x.length ≤ Rigid.nrm (Rigid.Dx (compMat A (sccOf A q)) x)) ∧
      HasEdge A (sccOf A q) := by
  obtain ⟨q, hq⟩ := top_rigid A hG hdiag hLC
  have hSC := sc_compMat A q
  obtain ⟨c, hc, hlow⟩ := Rigid.uniform_lower_Dx _ hSC hq
  refine ⟨q, hSC, hq, ⟨c, hc, hlow⟩, ?_⟩
  -- The product of `[0]` is non-zero, so there is an internal edge
  have h0 := hlow [0]
  have hpos : 0 < Rigid.nrm (Rigid.Dx (compMat A (sccOf A q)) [0]) :=
    lt_of_lt_of_le (mul_pos hc (pow_pos (by linarith) _)) h0
  by_contra hne
  have hz := compMat_eq_zero_of_not_hasEdge A q hne 0
  have : Rigid.Dx (compMat A (sccOf A q)) [0] = 0 := by
    rw [Rigid.Dx_singleton]
    ext x y
    simp [Rigid.DR, hz]
  rw [this] at hpos
  simp [Rigid.nrm] at hpos

/-- **From `top_rigid` to a heavy family of words** (Corollary 11.4, passed to Proposition 11.13; Proposition D.5 for the entries of the whole automaton): under the hypotheses of `top_rigid`
there are an index `a`, a word `Ψ`, `h ≥ 1` and `c > 0` with `c G^{|ω_ε|} ≤ (B_{ω_ε})_{aa}` for all `ε`
(`ω_ε := heavyWord Ψ h ε`, `heavy_family` of Appendix D). -/
theorem top_heavy (A : ValAuto Q) {G : ℝ} (hG : 1 < G)
    (hdiag : ∀ (w : List (Fin 2)) (i : Q), Rigid.Dx A.B w i i ≤ G ^ w.length)
    (hLC : ∀ κ : ℕ, 1 ≤ κ → (κ : ℝ) * Real.log G ≤ Rigid.bAvg A.B κ) :
    ∃ (a : Q) (Ψ : List (Fin 2)) (h : ℕ) (c : ℝ), 1 ≤ h ∧ 0 < c ∧
      ∀ ε : List (Fin 2), c * G ^ (Rigid.heavyWord Ψ h ε).length ≤ Rigid.Dx A.B (Rigid.heavyWord Ψ h ε) a a := by
  obtain ⟨q, hq⟩ := top_rigid A hG hdiag hLC
  obtain ⟨Ψ, h, a, c, hh, hc, hw⟩ := Rigid.heavy_family _ (sc_compMat A q) hq
  refine ⟨a.1, Ψ, h, c, hh, hc, fun ε => ?_⟩
  rw [← W2b.Dx_compMat_apply]
  exact hw ε

/-- **The component of the conclusion is a top component** (a check prompted by internal review; not needed downstream): under the hypotheses of `top_rigid`, for some `q`
the component `sccOf A q` is rigid at `G`, has an internal edge, and its diagonal `g` is exactly `G` (`gDiag (D^S) = G`).
`g_S ≤ G` follows from the diagonal bound, and `G ≤ g_S` from the uniform lower bound and Lemma D.2 (`entry_bound`). -/
theorem top_rigid_isTop (A : ValAuto Q) {G : ℝ} (hG : 1 < G)
    (hdiag : ∀ (w : List (Fin 2)) (i : Q), Rigid.Dx A.B w i i ≤ G ^ w.length)
    (hLC : ∀ κ : ℕ, 1 ≤ κ → (κ : ℝ) * Real.log G ≤ Rigid.bAvg A.B κ) :
    ∃ q, Rigid.RigidAt (compMat A (sccOf A q)) G ∧ HasEdge A (sccOf A q) ∧
      Rigid.gDiag (compMat A (sccOf A q)) = G := by
  obtain ⟨q, hSC, hR, ⟨c, hc, hlow⟩, hE⟩ := top_rigid' A hG hdiag hLC
  refine ⟨q, hR, hE, le_antisymm ?_ ?_⟩
  · -- `g_S ≤ G`
    unfold Rigid.gDiag
    refine Real.iSup_le (fun p => ?_) (by linarith)
    have hn : p.1.1.length ≠ 0 := by simpa [List.length_eq_zero_iff] using p.1.2
    have h1 := W2b.diag_compMat A hdiag q p.1.1 p.2
    calc (Rigid.Dx (compMat A (sccOf A q)) p.1.1 p.2 p.2) ^ ((p.1.1.length : ℝ)⁻¹)
        ≤ (G ^ p.1.1.length) ^ ((p.1.1.length : ℝ)⁻¹) :=
          Real.rpow_le_rpow (Rigid.Dx_nonneg _ _ _ _) h1 (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = G := Real.pow_rpow_inv_natCast (by linarith) hn
  · -- `G ≤ g_S`
    set g := Rigid.gDiag (compMat A (sccOf A q)) with hg
    have hg1 : 1 ≤ g := one_le_gComp A q hE
    obtain ⟨L, hL⟩ := Rigid.entry_bound _ hSC hg1 (Rigid.diag_le_gDiag _)
    set k : ℝ := (Fintype.card (sccOf A q) : ℝ) ^ 2 * g ^ L with hk
    have hup : ∀ n : ℕ, c * G ^ n ≤ k * g ^ n := by
      intro n
      have h1 := hlow (List.replicate n 0)
      rw [List.length_replicate] at h1
      have h2 : Rigid.nrm (Rigid.Dx (compMat A (sccOf A q)) (List.replicate n 0)) ≤
          (Fintype.card (sccOf A q) : ℝ) ^ 2 * g ^ (n + L) := by
        refine Rigid.nrm_le_of_entry_le fun i j => ?_
        rw [abs_of_nonneg (Rigid.Dx_nonneg _ _ _ _)]
        have := hL (List.replicate n 0) i j
        rwa [List.length_replicate] at this
      refine h1.trans (h2.trans (le_of_eq ?_))
      rw [hk, pow_add]; ring
    by_contra hlt
    push Not at hlt
    have hg0 : 0 < g := by linarith
    have hr : 1 < G / g := by rw [one_lt_div hg0]; exact hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (k / c) hr
    have h1 := hup n
    have hgn : 0 < g ^ n := pow_pos hg0 n
    have h2 : c * (G / g) ^ n ≤ k := by
      rw [div_pow, mul_div_assoc', div_le_iff₀ hgn]; exact h1
    have h3 : k < c * (G / g) ^ n := by
      rw [div_lt_iff₀ hc] at hn; linarith
    linarith

end Collatz.Arctic.NatQ5
