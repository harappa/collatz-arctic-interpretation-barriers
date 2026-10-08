/-
# Lemma 11.1 and Corollary 11.2: splitting paths into segments (counting the segments equal to `z`) and a polynomial bound

Lemma 11.1 (the growth of products) in the form that counts the segments equal to a given word `z`.
A statement about automata only, independent of $\mathcal T$ (`S_T`) and of rewriting rules.

* **Splitting at the first segment that leaves a component** (§2, `first_exit`): for a set `S`, `i ∈ S` and `j ∉ S`, with a sum over all splittings
  `bs = pre ++ c :: post` of the sequence of segments,
  `(B_{bs})_{ij} ≤ Σ_{splittings} Σ_{k ∈ S} Σ_{l ∉ S} (B_{pre})_{ik} (B_c)_{kl} (B_{post})_{lj}`.
  An earlier argument splits letter by letter; here we split **segment by segment (words of length `κ`)**: the segment `c` that contains the letter leaving the component
  is bounded as a whole by the one-letter bound `W^κ`, so the parts `pre` and `post` remain sequences of segments and the positions of the segments do not shift.
  In exchange, one segment is lost at each change of component (the `- p` in `θ^{#z - p}`).
* **The bound counting the segments equal to `z`** (§3, `path_block_bound`): if on each component
  `(D^S_{bs})_{xy} ≤ C G^{|bs|} θ^{#z(bs)}` (`#z(bs)` is the number of segments `z` in the sequence), then on the whole automaton
  `θ^{|Q|} (B_{bs})_{ij} ≤ C' (m + 1)^{|Q|} G^{|bs|} θ^{#z(bs)}` (`m` is the number of segments). The strong induction is on the
  potential `reachCnt` of the DAG of components (the number of indices reachable from `i`, `Compartment.lean`). No sums over subtypes are used
  (an anticipated difficulty did not arise).
* **The polynomial bound** (§4, `poly_bound`, `poly_bound_of_diag`; Corollary 11.2): the case `θ = 1`, `κ = 1`:
  `(B_w)_{ij} ≤ C' (|w| + 1)^{|Q|} G^{|w|}` (with `|Q|` in place of `m_* - 1` of an earlier version). The latter assumes only
  the diagonal bound `(B_w)_{ii} ≤ G^{|w|}` (the bound on each component comes from `entry_bound` of Appendix D) and
  is used in Proposition 11.13. The form for values `aval_poly_bound` (`V(w) ≤ C (|w| + 1)^{|Q|} G^{|w|}`) is also given.

`C'` depends only on `C`, `G`, the one-letter bound, `|Q|` and `κ`, and not on `θ` or `z` (`θ^{|Q|}` is put on the left).
-/
import CollatzProof.Arctic.Nat.Compartment

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Matrix

set_option linter.unusedSectionVars false

namespace W2b

/-! ## §1 Sums over the splittings of a sequence of segments -/

/-- The sum over all splittings of a sequence of segments `bs` into `pre ++ c :: post` (`c` is one segment). -/
def splitSum {M : Type*} [AddCommMonoid M] :
    (List (List (Fin 2)) → List (Fin 2) → List (List (Fin 2)) → M) → List (List (Fin 2)) → M
  | _, [] => 0
  | f, b :: bs => f [] b bs + splitSum (fun pre c post => f (b :: pre) c post) bs

section Split

variable {M : Type*} [AddCommMonoid M]

@[simp] theorem splitSum_nil (f : List (List (Fin 2)) → List (Fin 2) → List (List (Fin 2)) → M) :
    splitSum f [] = 0 := rfl

theorem splitSum_cons (f : List (List (Fin 2)) → List (Fin 2) → List (List (Fin 2)) → M)
    (b : List (Fin 2)) (bs : List (List (Fin 2))) :
    splitSum f (b :: bs) = f [] b bs + splitSum (fun pre c post => f (b :: pre) c post) bs := rfl

end Split

theorem splitSum_mul_left (r : ℝ) (bs : List (List (Fin 2))) :
    ∀ f : List (List (Fin 2)) → List (Fin 2) → List (List (Fin 2)) → ℝ,
      r * splitSum f bs = splitSum (fun pre c post => r * f pre c post) bs := by
  induction bs with
  | nil => intro f; simp
  | cons b bs ih =>
    intro f
    rw [splitSum_cons, splitSum_cons, mul_add, ih]

theorem splitSum_finset_sum {ι : Type*} (s : Finset ι) (bs : List (List (Fin 2))) :
    ∀ g : ι → List (List (Fin 2)) → List (Fin 2) → List (List (Fin 2)) → ℝ,
      ∑ k ∈ s, splitSum (g k) bs = splitSum (fun pre c post => ∑ k ∈ s, g k pre c post) bs := by
  induction bs with
  | nil => intro g; simp
  | cons b bs ih =>
    intro g
    simp only [splitSum_cons, Finset.sum_add_distrib]
    rw [ih (fun k pre c post => g k (b :: pre) c post)]

theorem splitSum_mono (bs : List (List (Fin 2))) :
    ∀ {f g : List (List (Fin 2)) → List (Fin 2) → List (List (Fin 2)) → ℝ},
      (∀ pre c post, f pre c post ≤ g pre c post) → splitSum f bs ≤ splitSum g bs := by
  induction bs with
  | nil => intro f g _; simp
  | cons b bs ih =>
    intro f g h
    rw [splitSum_cons, splitSum_cons]
    exact add_le_add (h _ _ _) (ih fun pre c post => h _ _ _)

/-- If each term is at most `M`, the sum is at most `|bs| M` (there are `|bs|` splittings). -/
theorem splitSum_le {M : ℝ} (bs : List (List (Fin 2))) :
    ∀ f : List (List (Fin 2)) → List (Fin 2) → List (List (Fin 2)) → ℝ,
      (∀ pre c post, pre ++ c :: post = bs → f pre c post ≤ M) → splitSum f bs ≤ bs.length * M := by
  induction bs with
  | nil => intro f _; simp
  | cons b bs ih =>
    intro f h
    rw [splitSum_cons, List.length_cons]
    have h1 : f [] b bs ≤ M := h [] b bs rfl
    have h2 := ih (fun pre c post => f (b :: pre) c post) fun pre c post hs => by
      refine h (b :: pre) c post ?_
      rw [List.cons_append, hs]
    push_cast
    linarith

/-! ## §2 Splitting at the first segment that leaves a component -/

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- **Splitting at the first segment that leaves `S`**: if `i ∈ S` and `j ∉ S`, then
`(B_{bs})_{ij} ≤ Σ_{bs = pre ++ c :: post} Σ_{k ∈ S} Σ_{l ∉ S} (B_{pre})_{ik} (B_c)_{kl} (B_{post})_{lj}`
(`B_{bs}` is the product of the concatenated segments). `S` may be any set. -/
theorem first_exit (B : Fin 2 → Matrix Q Q ℕ) (S : Finset Q) (bs : List (List (Fin 2))) :
    ∀ (i j : Q), i ∈ S → j ∉ S →
      Rigid.Dx B bs.flatten i j ≤ splitSum (fun pre c post => ∑ k ∈ S, ∑ l ∈ Sᶜ,
        Rigid.Dx B pre.flatten i k * Rigid.Dx B c k l * Rigid.Dx B post.flatten l j) bs := by
  induction bs with
  | nil =>
    intro i j hi hj
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    simp [hij]
  | cons b bs ih =>
    intro i j hi hj
    rw [List.flatten_cons, Rigid.Dx_append, Matrix.mul_apply, ← Finset.sum_add_sum_compl S, splitSum_cons,
      add_comm]
    refine add_le_add (le_of_eq ?_) ?_
    · -- The terms that leave `S` in the first segment
      rw [List.flatten_nil, Rigid.Dx_nil, Finset.sum_eq_single_of_mem i hi]
      · simp
      · intro k _ hk
        simp [Ne.symm hk]
    · -- The terms still in `S` after the first segment: apply the induction hypothesis with `k ∈ S` and put the first segment into the front part
      calc ∑ k ∈ S, Rigid.Dx B b i k * Rigid.Dx B bs.flatten k j
          ≤ ∑ k ∈ S, Rigid.Dx B b i k * splitSum (fun pre c post => ∑ k' ∈ S, ∑ l ∈ Sᶜ,
              Rigid.Dx B pre.flatten k k' * Rigid.Dx B c k' l * Rigid.Dx B post.flatten l j) bs :=
            Finset.sum_le_sum fun k hk =>
              mul_le_mul_of_nonneg_left (ih k j hk hj) (Rigid.Dx_nonneg B b i k)
        _ = splitSum (fun pre c post => ∑ k ∈ S, Rigid.Dx B b i k * ∑ k' ∈ S, ∑ l ∈ Sᶜ,
              Rigid.Dx B pre.flatten k k' * Rigid.Dx B c k' l * Rigid.Dx B post.flatten l j) bs :=
            (Finset.sum_congr rfl fun k _ => splitSum_mul_left _ _ _).trans (splitSum_finset_sum S bs _)
        _ ≤ splitSum (fun pre c post => ∑ k' ∈ S, ∑ l ∈ Sᶜ,
              Rigid.Dx B (b :: pre).flatten i k' * Rigid.Dx B c k' l * Rigid.Dx B post.flatten l j) bs := by
            refine splitSum_mono bs fun pre c post => ?_
            -- `Σ_{k ∈ S} (B_b)_{ik} (B_{pre})_{kk'} ≤ (B_{b pre})_{ik'}`
            have hrow : ∀ k', ∑ k ∈ S, Rigid.Dx B b i k * Rigid.Dx B pre.flatten k k' ≤
                Rigid.Dx B (b :: pre).flatten i k' := by
              intro k'
              rw [List.flatten_cons, Rigid.Dx_append, Matrix.mul_apply]
              exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun k _ _ =>
                mul_nonneg (Rigid.Dx_nonneg B _ _ _) (Rigid.Dx_nonneg B _ _ _)
            have e : ∑ k ∈ S, Rigid.Dx B b i k * ∑ k' ∈ S, ∑ l ∈ Sᶜ,
                Rigid.Dx B pre.flatten k k' * Rigid.Dx B c k' l * Rigid.Dx B post.flatten l j =
                ∑ k' ∈ S, ∑ l ∈ Sᶜ, (∑ k ∈ S, Rigid.Dx B b i k * Rigid.Dx B pre.flatten k k') *
                  (Rigid.Dx B c k' l * Rigid.Dx B post.flatten l j) := by
              calc ∑ k ∈ S, Rigid.Dx B b i k * ∑ k' ∈ S, ∑ l ∈ Sᶜ,
                    Rigid.Dx B pre.flatten k k' * Rigid.Dx B c k' l * Rigid.Dx B post.flatten l j
                  = ∑ k ∈ S, ∑ k' ∈ S, ∑ l ∈ Sᶜ, Rigid.Dx B b i k *
                      (Rigid.Dx B pre.flatten k k' * Rigid.Dx B c k' l * Rigid.Dx B post.flatten l j) := by
                    simp only [Finset.mul_sum]
                _ = ∑ k' ∈ S, ∑ k ∈ S, ∑ l ∈ Sᶜ, Rigid.Dx B b i k *
                      (Rigid.Dx B pre.flatten k k' * Rigid.Dx B c k' l * Rigid.Dx B post.flatten l j) :=
                    Finset.sum_comm
                _ = ∑ k' ∈ S, ∑ l ∈ Sᶜ, ∑ k ∈ S, Rigid.Dx B b i k *
                      (Rigid.Dx B pre.flatten k k' * Rigid.Dx B c k' l * Rigid.Dx B post.flatten l j) :=
                    Finset.sum_congr rfl fun k' _ => Finset.sum_comm
                _ = ∑ k' ∈ S, ∑ l ∈ Sᶜ, (∑ k ∈ S, Rigid.Dx B b i k * Rigid.Dx B pre.flatten k k') *
                      (Rigid.Dx B c k' l * Rigid.Dx B post.flatten l j) := by
                    refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun l _ => ?_
                    rw [Finset.sum_mul]
                    exact Finset.sum_congr rfl fun k _ => by ring
            rw [e]
            refine Finset.sum_le_sum fun k' _ => Finset.sum_le_sum fun l _ => ?_
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_right (hrow k')
              (mul_nonneg (Rigid.Dx_nonneg B _ _ _) (Rigid.Dx_nonneg B _ _ _))

/-! ## §3 The bound counting the segments equal to `z` -/

/-- The constants of the induction, `N_0 = a`, `N_{r+1} = a + b N_r`. -/
def nBound (a b : ℝ) : ℕ → ℝ
  | 0 => a
  | r + 1 => a + b * nBound a b r

theorem nBound_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : ∀ r, 0 ≤ nBound a b r
  | 0 => ha
  | r + 1 => add_nonneg ha (mul_nonneg hb (nBound_nonneg ha hb r))

/-- The norm of the product of a word is at most `|K| W^{|w|}` (`W` is the one-letter bound `Wd` of Appendix D). -/
theorem nrm_Dx_le {K : Type*} [Fintype K] [DecidableEq K] (D : Fin 2 → Matrix K K ℕ) :
    ∀ w : List (Fin 2), Rigid.nrm (Rigid.Dx D w) ≤ Fintype.card K * Rigid.Wd D ^ w.length
  | [] => by simp [Rigid.nrm_one]
  | b :: w => by
    rw [Rigid.Dx_cons, List.length_cons, pow_succ]
    calc Rigid.nrm (Rigid.DR D b * Rigid.Dx D w) ≤ Rigid.nrm (Rigid.DR D b) * Rigid.nrm (Rigid.Dx D w) :=
          Rigid.nrm_mul_le _ _
      _ ≤ Rigid.Wd D * (Fintype.card K * Rigid.Wd D ^ w.length) :=
          mul_le_mul (Rigid.nrm_DR_le D b) (nrm_Dx_le D w) (Rigid.nrm_nonneg _)
            (by linarith [Rigid.one_le_Wd D])
      _ = Fintype.card K * (Rigid.Wd D ^ w.length * Rigid.Wd D) := by ring

theorem reachCnt_pos (A : ValAuto Q) (i : Q) : 1 ≤ reachCnt A i := by
  classical
  unfold reachCnt
  exact Finset.card_pos.2 ⟨i, by simp [conn_refl]⟩

theorem reachCnt_le_card (A : ValAuto Q) (i : Q) : reachCnt A i ≤ Fintype.card Q := by
  classical
  unfold reachCnt
  exact Finset.card_le_univ _

/-- Lengths and numbers of segments in a splitting of a sequence of segments. -/
theorem split_props {κ : ℕ} {z : List (Fin 2)} {pre post bs : List (List (Fin 2))} {c : List (Fin 2)}
    (hs : pre ++ c :: post = bs) (hbs : ∀ b ∈ bs, b.length = κ) :
    (∀ b ∈ pre, b.length = κ) ∧ c.length = κ ∧ (∀ b ∈ post, b.length = κ) ∧
      bs.flatten.length = pre.flatten.length + κ + post.flatten.length ∧
      bs.count z ≤ pre.count z + 1 + post.count z ∧ post.length ≤ bs.length := by
  subst hs
  refine ⟨fun b hb => hbs b (by simp [hb]), hbs c (by simp), fun b hb => hbs b (by simp [hb]), ?_, ?_, ?_⟩
  · rw [List.flatten_append, List.flatten_cons, List.length_append, List.length_append, hbs c (by simp)]
    ring
  · rw [List.count_append, List.count_cons]
    split <;> omega
  · simp only [List.length_append, List.length_cons]; omega

/-- **The path bound counting the segments equal to `z`** (raw form): if `(B_{bs})_{ik} ≤ C G^{|bs|} θ^{#z(bs)}` for the pairs with `k ∈ sccOf A i`
(segments of length `κ`), then on the whole automaton
`θ^{|Q|} (B_{bs})_{ij} ≤ C' (m + 1)^{|Q|} G^{|bs|} θ^{#z(bs)}` (`m` is the number of segments). -/
theorem path_bound_raw (A : ValAuto Q) {G θ C : ℝ} {κ : ℕ} {z : List (Fin 2)} (hG : 1 ≤ G) (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1)
    (hS : ∀ i k, k ∈ sccOf A i → ∀ bs : List (List (Fin 2)), (∀ b ∈ bs, b.length = κ) →
      Rigid.Dx A.B bs.flatten i k ≤ C * G ^ bs.flatten.length * θ ^ bs.count z) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ bs : List (List (Fin 2)), (∀ b ∈ bs, b.length = κ) → ∀ i j,
      θ ^ Fintype.card Q * Rigid.Dx A.B bs.flatten i j ≤
        C' * ((bs.length : ℝ) + 1) ^ Fintype.card Q * G ^ bs.flatten.length * θ ^ bs.count z := by
  set Cp : ℝ := max C 0 with hCp
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  have hCCp : C ≤ Cp := le_max_left _ _
  set V : ℝ := (Fintype.card Q : ℝ) * Rigid.Wd A.B ^ κ with hV
  have hV0 : 0 ≤ V := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith [Rigid.one_le_Wd A.B]) _)
  have hVc : ∀ c : List (Fin 2), c.length = κ → ∀ k l, Rigid.Dx A.B c k l ≤ V := by
    intro c hc k l
    have := (Rigid.le_nrm _ k l).trans (nrm_Dx_le A.B c)
    rwa [hc] at this
  set b0 : ℝ := (Fintype.card Q : ℝ) ^ 2 * Cp * V with hb0
  have hb00 : 0 ≤ b0 := mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hCp0) hV0
  set N := nBound Cp b0 with hN
  have hN0 : ∀ r, 0 ≤ N r := nBound_nonneg hCp0 hb00
  have hG0 : 0 < G := by linarith
  -- The bound inside a component (`C` replaced by `Cp`)
  have hS' : ∀ i k, k ∈ sccOf A i → ∀ bs : List (List (Fin 2)), (∀ b ∈ bs, b.length = κ) →
      Rigid.Dx A.B bs.flatten i k ≤ Cp * G ^ bs.flatten.length * θ ^ bs.count z := by
    intro i k hk bs hbs
    refine (hS i k hk bs hbs).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCCp (pow_nonneg hG0.le _))
      (pow_nonneg hθ0.le _)
  -- The statement of the induction
  have claim : ∀ r : ℕ, ∀ i, reachCnt A i ≤ r → ∀ bs : List (List (Fin 2)), (∀ b ∈ bs, b.length = κ) →
      ∀ j, θ ^ r * Rigid.Dx A.B bs.flatten i j ≤
        N r * ((bs.length : ℝ) + 1) ^ r * G ^ bs.flatten.length * θ ^ bs.count z := by
    intro r
    induction r with
    | zero =>
      intro i hi
      exact absurd hi (by have := reachCnt_pos A i; omega)
    | succ r ih =>
      intro i hi bs hbs j
      set S := sccOf A i with hSdef
      have hiS : i ∈ S := self_mem_sccOf A i
      set m : ℝ := (bs.length : ℝ) + 1 with hm
      have hm1 : 1 ≤ m := by simp [hm]
      have hθr : θ ^ (r + 1) ≤ 1 := pow_le_one₀ hθ0.le hθ1
      have hGθ : 0 ≤ G ^ bs.flatten.length * θ ^ bs.count z :=
        mul_nonneg (pow_nonneg hG0.le _) (pow_nonneg hθ0.le _)
      have hNs : N (r + 1) = Cp + b0 * N r := rfl
      by_cases hj : j ∈ S
      · -- `j` is also in the component of `i`: the bound inside the component
        have h1 := hS' i j hj bs hbs
        have hx0 := Rigid.Dx_nonneg A.B bs.flatten i j
        calc θ ^ (r + 1) * Rigid.Dx A.B bs.flatten i j ≤ Rigid.Dx A.B bs.flatten i j :=
              mul_le_of_le_one_left hx0 hθr
          _ ≤ Cp * G ^ bs.flatten.length * θ ^ bs.count z := h1
          _ = Cp * 1 * (G ^ bs.flatten.length * θ ^ bs.count z) := by ring
          _ ≤ N (r + 1) * m ^ (r + 1) * (G ^ bs.flatten.length * θ ^ bs.count z) := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul ?_ (one_le_pow₀ hm1) zero_le_one ?_) hGθ
              · rw [hNs]; linarith [mul_nonneg hb00 (hN0 r)]
              · exact hN0 _
          _ = N (r + 1) * m ^ (r + 1) * G ^ bs.flatten.length * θ ^ bs.count z := by ring
      · -- `j` is outside the component: split at the first segment that leaves it
        have hfe := first_exit A.B S bs i j hiS hj
        set T : ℝ := Cp * V * N r * m ^ r * (G ^ bs.flatten.length * θ ^ bs.count z) with hT
        have hT0 : 0 ≤ T :=
          mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCp0 hV0) (hN0 r)) (pow_nonneg (by linarith) _)) hGθ
        -- The term of one `(k, l)` of one splitting
        have hterm : ∀ pre c post, pre ++ c :: post = bs → ∀ k ∈ S, ∀ l ∈ Sᶜ,
            θ ^ (r + 1) * (Rigid.Dx A.B pre.flatten i k * Rigid.Dx A.B c k l *
              Rigid.Dx A.B post.flatten l j) ≤ T := by
          intro pre c post hs k hk l hl
          obtain ⟨hpre, hc, hpost, hlen, hcnt, hplen⟩ := split_props (z := z) hs hbs
          rcases Rigid.Dx_entry_zero_or_one_le A.B c k l with h0 | h1
          · rw [h0]; simpa using hT0
          · -- `l` is reachable from `i` and outside the component
            have hconn_ik : Conn A i k := ((mem_sccOf A).1 hk).1
            have hkl : 1 ≤ Rigid.DxN A.B c k l := by
              rw [Rigid.Dx_apply] at h1; exact_mod_cast h1
            have hconn_il : Conn A i l := conn_trans A hconn_ik (conn_of_DxN A hkl)
            have hlS : l ∉ sccOf A i := Finset.mem_compl.1 hl
            have hlr : reachCnt A l ≤ r := by
              have := reachCnt_lt A hconn_il hlS; omega
            have hpost' := ih l hlr post hpost j
            have hpre' := hS' i k hk pre hpre
            have hc' := hVc c hc k l
            have e1 : θ ^ (r + 1) * (Rigid.Dx A.B pre.flatten i k * Rigid.Dx A.B c k l *
                Rigid.Dx A.B post.flatten l j) = Rigid.Dx A.B pre.flatten i k * Rigid.Dx A.B c k l * θ *
                  (θ ^ r * Rigid.Dx A.B post.flatten l j) := by ring
            rw [e1]
            have hP0 := Rigid.Dx_nonneg A.B pre.flatten i k
            have hc0 := Rigid.Dx_nonneg A.B c k l
            have step1 : Rigid.Dx A.B pre.flatten i k * Rigid.Dx A.B c k l * θ *
                (θ ^ r * Rigid.Dx A.B post.flatten l j) ≤
                (Cp * G ^ pre.flatten.length * θ ^ pre.count z) * V * θ *
                  (N r * ((post.length : ℝ) + 1) ^ r * G ^ post.flatten.length * θ ^ post.count z) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul hpre' hc' hc0 ?_) hθ0.le) hpost'
                (mul_nonneg (pow_nonneg hθ0.le _) (Rigid.Dx_nonneg A.B _ _ _)) ?_
              · exact mul_nonneg (mul_nonneg hCp0 (pow_nonneg hG0.le _)) (pow_nonneg hθ0.le _)
              · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCp0 (pow_nonneg hG0.le _))
                  (pow_nonneg hθ0.le _)) hV0) hθ0.le
            refine step1.trans ?_
            -- Comparing the exponents
            have hGp : G ^ pre.flatten.length * G ^ post.flatten.length ≤ G ^ bs.flatten.length := by
              rw [← pow_add, hlen]
              exact pow_le_pow_right₀ hG (by omega)
            have hθp : θ ^ pre.count z * θ * θ ^ post.count z ≤ θ ^ bs.count z := by
              rw [← pow_succ, ← pow_add]
              exact pow_le_pow_of_le_one hθ0.le hθ1 (by omega)
            have hmp : ((post.length : ℝ) + 1) ^ r ≤ m ^ r := by
              refine pow_le_pow_left₀ (by positivity) ?_ r
              simp only [hm]
              exact_mod_cast Nat.add_le_add_right hplen 1
            have e2 : (Cp * G ^ pre.flatten.length * θ ^ pre.count z) * V * θ *
                (N r * ((post.length : ℝ) + 1) ^ r * G ^ post.flatten.length * θ ^ post.count z) =
                Cp * V * N r * ((post.length : ℝ) + 1) ^ r *
                  ((G ^ pre.flatten.length * G ^ post.flatten.length) *
                    (θ ^ pre.count z * θ * θ ^ post.count z)) := by ring
            rw [e2, hT]
            have hCVN : 0 ≤ Cp * V * N r := mul_nonneg (mul_nonneg hCp0 hV0) (hN0 r)
            have hθq : 0 ≤ θ ^ pre.count z * θ * θ ^ post.count z :=
              mul_nonneg (mul_nonneg (pow_nonneg hθ0.le _) hθ0.le) (pow_nonneg hθ0.le _)
            refine mul_le_mul (mul_le_mul_of_nonneg_left hmp hCVN)
              (mul_le_mul hGp hθp hθq (pow_nonneg hG0.le _))
              (mul_nonneg (mul_nonneg (pow_nonneg hG0.le _) (pow_nonneg hG0.le _)) hθq) ?_
            exact mul_nonneg hCVN (pow_nonneg (by linarith) _)
        -- The sum for each splitting
        have hsplit : ∀ pre c post, pre ++ c :: post = bs →
            θ ^ (r + 1) * (∑ k ∈ S, ∑ l ∈ Sᶜ, Rigid.Dx A.B pre.flatten i k * Rigid.Dx A.B c k l *
              Rigid.Dx A.B post.flatten l j) ≤ (Fintype.card Q : ℝ) ^ 2 * T := by
          intro pre c post hs
          rw [Finset.mul_sum]
          calc ∑ k ∈ S, θ ^ (r + 1) * ∑ l ∈ Sᶜ, Rigid.Dx A.B pre.flatten i k * Rigid.Dx A.B c k l *
                Rigid.Dx A.B post.flatten l j
              ≤ ∑ _k ∈ S, ∑ _l ∈ Sᶜ, T := by
                refine Finset.sum_le_sum fun k hk => ?_
                rw [Finset.mul_sum]
                exact Finset.sum_le_sum fun l hl => hterm pre c post hs k hk l hl
            _ = (S.card : ℝ) * (Sᶜ.card : ℝ) * T := by
                simp only [Finset.sum_const, nsmul_eq_mul]; ring
            _ ≤ (Fintype.card Q : ℝ) ^ 2 * T := by
                refine mul_le_mul_of_nonneg_right ?_ hT0
                have h1 : (S.card : ℝ) ≤ Fintype.card Q := by exact_mod_cast Finset.card_le_univ S
                have h2 : (Sᶜ.card : ℝ) ≤ Fintype.card Q := by exact_mod_cast Finset.card_le_univ Sᶜ
                rw [sq]
                exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        have hsum : θ ^ (r + 1) * Rigid.Dx A.B bs.flatten i j ≤
            (bs.length : ℝ) * ((Fintype.card Q : ℝ) ^ 2 * T) := by
          calc θ ^ (r + 1) * Rigid.Dx A.B bs.flatten i j
              ≤ θ ^ (r + 1) * splitSum (fun pre c post => ∑ k ∈ S, ∑ l ∈ Sᶜ,
                  Rigid.Dx A.B pre.flatten i k * Rigid.Dx A.B c k l * Rigid.Dx A.B post.flatten l j) bs :=
                mul_le_mul_of_nonneg_left hfe (pow_nonneg hθ0.le _)
            _ = splitSum (fun pre c post => θ ^ (r + 1) * ∑ k ∈ S, ∑ l ∈ Sᶜ,
                  Rigid.Dx A.B pre.flatten i k * Rigid.Dx A.B c k l * Rigid.Dx A.B post.flatten l j) bs :=
                splitSum_mul_left _ _ _
            _ ≤ (bs.length : ℝ) * ((Fintype.card Q : ℝ) ^ 2 * T) := splitSum_le bs _ hsplit
        refine hsum.trans ?_
        -- `|bs| |Q|^2 T ≤ N_{r+1} m^{r+1} G^{|bs|} θ^{#z}`
        have hlen_m : (bs.length : ℝ) ≤ m := by simp [hm]
        have e3 : (bs.length : ℝ) * ((Fintype.card Q : ℝ) ^ 2 * T) =
            b0 * N r * ((bs.length : ℝ) * m ^ r) * (G ^ bs.flatten.length * θ ^ bs.count z) := by
          rw [hT, hb0]; ring
        rw [e3]
        have hb0N : 0 ≤ b0 * N r := mul_nonneg hb00 (hN0 r)
        calc b0 * N r * ((bs.length : ℝ) * m ^ r) * (G ^ bs.flatten.length * θ ^ bs.count z)
            ≤ b0 * N r * m ^ (r + 1) * (G ^ bs.flatten.length * θ ^ bs.count z) := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hb0N) hGθ
              rw [pow_succ, mul_comm]
              exact mul_le_mul_of_nonneg_left hlen_m (pow_nonneg (by linarith) _)
          _ ≤ N (r + 1) * m ^ (r + 1) * (G ^ bs.flatten.length * θ ^ bs.count z) := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (pow_nonneg (by linarith) _)) hGθ
              rw [hNs]; linarith
          _ = N (r + 1) * m ^ (r + 1) * G ^ bs.flatten.length * θ ^ bs.count z := by ring
  refine ⟨N (Fintype.card Q), hN0 _, fun bs hbs i j => ?_⟩
  exact claim (Fintype.card Q) i (reachCnt_le_card A i) bs hbs j

end W2b

/-! ## §3' The main theorem -/

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- **`path_block_bound` (Lemma 11.1, the form counting the segments equal to `z`)**:
if for every strongly connected component `S = sccOf A q` of the automaton `A` and every sequence `bs` of segments of length `κ`,
`(D^S_{bs})_{xy} ≤ C G^{|bs|} θ^{#z(bs)}` (`#z(bs) = bs.count z`), then there is `C' ≥ 0` such that for all sequences and indices
`θ^{|Q|} (B_{bs})_{ij} ≤ C' (m + 1)^{|Q|} G^{|bs|} θ^{#z(bs)}` (`m = bs.length`). `C'` does not depend on `θ` or `z`. -/
theorem path_block_bound (A : ValAuto Q) {G θ C : ℝ} {κ : ℕ} {z : List (Fin 2)} (hG : 1 ≤ G) (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1)
    (hS : ∀ q (bs : List (List (Fin 2))), (∀ b ∈ bs, b.length = κ) → ∀ x y : sccOf A q,
      (DC A (sccOf A q) bs.flatten x y : ℝ) ≤ C * G ^ bs.flatten.length * θ ^ bs.count z) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ bs : List (List (Fin 2)), (∀ b ∈ bs, b.length = κ) → ∀ i j,
      θ ^ Fintype.card Q * (Rigid.DxN A.B bs.flatten i j : ℝ) ≤
        C' * ((bs.length : ℝ) + 1) ^ Fintype.card Q * G ^ bs.flatten.length * θ ^ bs.count z := by
  have hS' : ∀ i k, k ∈ sccOf A i → ∀ bs : List (List (Fin 2)), (∀ b ∈ bs, b.length = κ) →
      Rigid.Dx A.B bs.flatten i k ≤ C * G ^ bs.flatten.length * θ ^ bs.count z := by
    intro i k hk bs hbs
    have h := hS i bs hbs ⟨i, self_mem_sccOf A i⟩ ⟨k, hk⟩
    rwa [DC_apply, ← Rigid.Dx_apply] at h
  obtain ⟨C', hC', h⟩ := W2b.path_bound_raw A hG hθ0 hθ1 hS'
  refine ⟨C', hC', fun bs hbs i j => ?_⟩
  rw [← Rigid.Dx_apply]
  exact h bs hbs i j

/-! ## §4 The polynomial bound (`θ = 1`, `κ = 1`) -/

/-- The entries of the real product of a word on a component are entries of the product on the whole automaton (also used in `top_rigid`). -/
theorem W2b.Dx_compMat_apply (A : ValAuto Q) (q : Q) (w : List (Fin 2)) (x y : sccOf A q) :
    Rigid.Dx (compMat A (sccOf A q)) w x y = Rigid.Dx A.B w x.1 y.1 := by
  rw [Rigid.Dx_apply, Rigid.Dx_apply]
  exact_mod_cast DC_apply A q w x y

/-- The diagonal bound on the whole automaton gives the diagonal bound on the components. -/
theorem W2b.diag_compMat (A : ValAuto Q) {G : ℝ}
    (hdiag : ∀ (w : List (Fin 2)) (i : Q), Rigid.Dx A.B w i i ≤ G ^ w.length) (q : Q) :
    ∀ (w : List (Fin 2)) (x : sccOf A q), Rigid.Dx (compMat A (sccOf A q)) w x x ≤ G ^ w.length := by
  intro w x
  rw [W2b.Dx_compMat_apply]
  exact hdiag w x.1

theorem W2b.flatten_map_singleton (w : List (Fin 2)) : (w.map fun b => [b]).flatten = w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [ih]

/-- **The polynomial bound `poly_bound`** (the case `θ = 1`, `κ = 1` of `path_block_bound`): if on every component
`(D^S_w)_{xy} ≤ C G^{|w|}`, then there is `C' ≥ 0` with `(B_w)_{ij} ≤ C' (|w| + 1)^{|Q|} G^{|w|}` for all words. -/
theorem poly_bound (A : ValAuto Q) {G C : ℝ} (hG : 1 ≤ G)
    (hS : ∀ q (w : List (Fin 2)) (x y : sccOf A q), (DC A (sccOf A q) w x y : ℝ) ≤ C * G ^ w.length) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (w : List (Fin 2)) (i j : Q),
      (Rigid.DxN A.B w i j : ℝ) ≤ C' * ((w.length : ℝ) + 1) ^ Fintype.card Q * G ^ w.length := by
  obtain ⟨C', hC', h⟩ := path_block_bound A (κ := 1) (z := []) (θ := 1) (C := C) hG one_pos le_rfl
    (fun q bs _ x y => by simpa using hS q bs.flatten x y)
  refine ⟨C', hC', fun w i j => ?_⟩
  have hv : ∀ b ∈ w.map (fun b => [b]), b.length = 1 := by
    intro b hb
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 hb
    rfl
  have := h (w.map fun b => [b]) hv i j
  simpa [W2b.flatten_map_singleton] using this

/-- **The polynomial bound, diagonal form `poly_bound_of_diag`**: if `G ≥ 1` and `(B_w)_{ii} ≤ G^{|w|}` for all words and indices, then
there is `C' ≥ 0` with `(B_w)_{ij} ≤ C' (|w| + 1)^{|Q|} G^{|w|}` for all words (the absence of entrywise defects
(Lemma D.2, `entry_bound` of Appendix D) is used on each component). -/
theorem poly_bound_of_diag (A : ValAuto Q) {G : ℝ} (hG : 1 ≤ G)
    (hdiag : ∀ (w : List (Fin 2)) (i : Q), Rigid.Dx A.B w i i ≤ G ^ w.length) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (w : List (Fin 2)) (i j : Q),
      (Rigid.DxN A.B w i j : ℝ) ≤ C' * ((w.length : ℝ) + 1) ^ Fintype.card Q * G ^ w.length := by
  have hdq := W2b.diag_compMat A hdiag
  have hL : ∀ q, ∃ L : ℕ, ∀ (w : List (Fin 2)) (x y : sccOf A q),
      Rigid.Dx (compMat A (sccOf A q)) w x y ≤ G ^ (w.length + L) :=
    fun q => Rigid.entry_bound _ (sc_compMat A q) hG (hdq q)
  choose L hL using hL
  set C : ℝ := ∑ q, G ^ L q with hC
  refine poly_bound A hG (C := C) fun q w x y => ?_
  have h1 := hL q w x y
  rw [Rigid.Dx_apply] at h1
  refine h1.trans ?_
  rw [pow_add, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (by linarith) _)
  exact Finset.single_le_sum (f := fun q => G ^ L q) (fun q _ => pow_nonneg (by linarith) _) (Finset.mem_univ q)

/-- **The polynomial bound for values** (Corollary 11.2; the form "`V(n) ≤ C ℓ(n)^p G^{ℓ(n)}`" used for Proposition 11.13): if `G ≥ 1` and the diagonal bound
`(B_w)_{ii} ≤ G^{|w|}` holds, then there is `C ≥ 0` with `aval A w ≤ C (|w| + 1)^{|Q|} G^{|w|}` for all words. -/
theorem aval_poly_bound (A : ValAuto Q) {G : ℝ} (hG : 1 ≤ G)
    (hdiag : ∀ (w : List (Fin 2)) (i : Q), Rigid.Dx A.B w i i ≤ G ^ w.length) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : List (Fin 2),
      (aval A w : ℝ) ≤ C * ((w.length : ℝ) + 1) ^ Fintype.card Q * G ^ w.length := by
  obtain ⟨C', hC', h⟩ := poly_bound_of_diag A hG hdiag
  set U : ℝ := ∑ i, ∑ j, (A.u i : ℝ) * (A.v j : ℝ) with hU
  have hU0 : 0 ≤ U := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  refine ⟨U * C', mul_nonneg hU0 hC', fun w => ?_⟩
  set R : ℝ := ((w.length : ℝ) + 1) ^ Fintype.card Q * G ^ w.length with hR
  have hR0 : 0 ≤ R := mul_nonneg (by positivity) (pow_nonneg (by linarith) _)
  rw [aval_eq_sum]
  push_cast
  calc ∑ i, ∑ j, (A.u i : ℝ) * (Rigid.DxN A.B w i j : ℝ) * (A.v j : ℝ)
      ≤ ∑ i, ∑ j, (A.u i : ℝ) * (A.v j : ℝ) * (C' * R) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        have hij : (Rigid.DxN A.B w i j : ℝ) ≤ C' * R := by rw [hR, ← mul_assoc]; exact h w i j
        calc (A.u i : ℝ) * (Rigid.DxN A.B w i j : ℝ) * (A.v j : ℝ)
            = (A.u i : ℝ) * (A.v j : ℝ) * (Rigid.DxN A.B w i j : ℝ) := by ring
          _ ≤ (A.u i : ℝ) * (A.v j : ℝ) * (C' * R) :=
              mul_le_mul_of_nonneg_left hij (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ = U * (C' * R) := by rw [hU, Finset.sum_mul]; simp_rw [Finset.sum_mul]
    _ = U * C' * (((w.length : ℝ) + 1) ^ Fintype.card Q * G ^ w.length) := by rw [hR]; ring
    _ = U * C' * ((w.length : ℝ) + 1) ^ Fintype.card Q * G ^ w.length := by ring

end Collatz.Arctic.NatQ5
