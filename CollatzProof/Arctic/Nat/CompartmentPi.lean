/-
# `π_C`, `u*`, Lemma 10.7 and (A^rel)

Continuation of `Compartment.lean` (Lemma 10.7, the remark after Corollary 10.9, and notions of an earlier, longer argument).

* **`π_C`** (§5): `piSum A C u L` (the sum of the entries of `D^C_w` over the words of length `L` that do not contain `u` as a factor) and `PiNeg`
  (`π_C(u) < 0` written as exponential decay: `piSum L ≤ c(2θ)^L` for some `0 ≤ θ < 1` and `c`; equivalent to the definition by limsup).
  The equivalence of `Decay2` (exponential decay of the sum of the entries of `A_C^L`) with `RhoLt` (`decay2_iff_rhoLt`), and `Decay2 → PiNeg`.
* **`u*` and Lemma 10.7** (§6): the support type `typ A w` of a word (a Boolean matrix, `MinIdeal.BRel`), the monoid of types `typMon A`,
  `IsUStar A u` (the type is an idempotent of the minimal ideal, as in Section 6). **Lemma 10.7** (`ustar_kills`): on a component that is not survivable,
  `D^C_{u*} = 0`. No assumption that the monoid avoids zero is needed. Second half: the sum for `π_C` equals the sum over all words (`piSum_eq_full`), and
  `π_C(u*) < 0 ⟺ ρ(A_C) < 2` (`piNeg_iff_rhoLt`).
* **The counting for (A^rel)** (§7): a non-empty 0/1 component that is not survivable has `ρ(A_C) < 2` (`rhoLt_of_zeroOne_kills`).
* **(A^rel)** (§8): `ARel A` (for some `u*`, every relevant strongly connected component outside `Q_{\mathrm s}` (survivable and 0/1)
  has `π_C(u*) < 0`). **If all components are 0/1, then (A^rel) holds** (`aRel_of_zeroOne`; the remark after Corollary 10.9).
-/
import CollatzProof.Arctic.Nat.Compartment

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Matrix

set_option linter.unusedSectionVars false

/-! ## §5 Sums over words and `π_C` -/

section Sums

variable {K : Type*} [Fintype K] [DecidableEq K]

theorem wsum_finset_sum {κ : Type*} (s : Finset κ) (L : ℕ) (F : κ → List (Fin 2) → ℝ) :
    Rigid.wsum L (fun w => ∑ k ∈ s, F k w) = ∑ k ∈ s, Rigid.wsum L (F k) := by
  induction L generalizing F with
  | zero => rfl
  | succ L ih =>
    simp only [Rigid.wsum_succ]
    simp_rw [ih]
    exact Finset.sum_comm

/-- The sum of `D_w` over the words of length `L` is `(D₀ + D₁)^L` (entrywise, real). -/
theorem wsum_DxN (D : Fin 2 → Matrix K K ℕ) (L : ℕ) (i j : K) :
    Rigid.wsum L (fun w => (Rigid.DxN D w i j : ℝ)) = (((D 0 + D 1) ^ L) i j : ℝ) := by
  induction L generalizing i with
  | zero => simp [Rigid.wsum_zero]
  | succ L ih =>
    rw [Rigid.wsum_succ]
    have hstep : ∀ b : Fin 2, Rigid.wsum L (fun w => (Rigid.DxN D (b :: w) i j : ℝ)) =
        ∑ k, (D b i k : ℝ) * (((D 0 + D 1) ^ L) k j : ℝ) := by
      intro b
      have : (fun w => (Rigid.DxN D (b :: w) i j : ℝ)) =
          fun w => ∑ k ∈ Finset.univ, (D b i k : ℝ) * (Rigid.DxN D w k j : ℝ) := by
        funext w
        rw [DxN_apply_cons]; push_cast; rfl
      rw [this, wsum_finset_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Rigid.wsum_mul_left, ih]
    simp_rw [hstep]
    rw [pow_succ', Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.add_apply]; push_cast; ring

/-- The sum over the words of length `L` of the sums of the entries of `D_w` is the sum of the entries of `(D₀ + D₁)^L`. -/
theorem wsum_esum (D : Fin 2 → Matrix K K ℕ) (L : ℕ) :
    Rigid.wsum L (fun w => (esum (Rigid.DxN D w) : ℝ)) = (esum ((D 0 + D 1) ^ L) : ℝ) := by
  have : (fun w => (esum (Rigid.DxN D w) : ℝ)) =
      fun w => ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, (Rigid.DxN D w i j : ℝ) := by
    funext w; simp [esum]
  rw [this, wsum_finset_sum]
  simp_rw [wsum_finset_sum, wsum_DxN]
  simp [esum]

end Sums

section Pi

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (A : ValAuto Q)

/-- The sum for `π_C(u)`: the sum of the entries of `D^C_w` over the words of length `L` that do not contain `u` as a factor (the quantity `a_L(C)`). -/
noncomputable def piSum (C : Finset Q) (u : List (Fin 2)) (L : ℕ) : ℝ :=
  Rigid.wsum L (fun w => if u <:+: w then 0 else (esum (DC A C w) : ℝ))

/-- **`π_C(u) < 0`** (the condition (H_<) of an earlier argument) written as exponential decay: for some `0 ≤ θ < 1` and `c`,
`piSum L ≤ c (2θ)^L` (equivalent to the negativity of `π_C := limsup (1/L) log(2^{-L} Σ ‖D^C_w‖_max)`; the sum of the entries and the largest
entry agree up to the factor `|C|^2`). -/
def PiNeg (C : Finset Q) (u : List (Fin 2)) : Prop :=
  ∃ θ c : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∀ L, piSum A C u L ≤ c * (2 * θ) ^ L

theorem piSum_le_full (C : Finset Q) (u : List (Fin 2)) (L : ℕ) :
    piSum A C u L ≤ (esum (AC A C ^ L) : ℝ) := by
  rw [AC, ← wsum_esum]
  refine Rigid.wsum_mono fun w _ => ?_
  split_ifs
  · exact Nat.cast_nonneg _
  · exact le_rfl

/-- If `A_C` decays exponentially (`ρ(A_C) < 2`), then `π_C(u) < 0` for every `u`. -/
theorem piNeg_of_decay2 (C : Finset Q) (u : List (Fin 2)) (h : Decay2 (AC A C)) : PiNeg A C u := by
  obtain ⟨θ, c, hθ0, hθ1, hb⟩ := h
  exact ⟨θ, c, hθ0, hθ1, fun L => (piSum_le_full A C u L).trans (hb L)⟩

/-! ## §6 `u*` and Lemma 10.7 -/

/-- The support type of a word (a Boolean matrix): `(B_w)_{ij} ≥ 1`. -/
def typ (w : List (Fin 2)) : MinIdeal.BRel Q := fun i j => 1 ≤ Rigid.DxN A.B w i j

theorem typ_nil : typ A [] = 1 :=
  MinIdeal.BRel.ext fun a b => by
    rw [MinIdeal.BRel.one_apply]
    show 1 ≤ (1 : Matrix Q Q ℕ) a b ↔ a = b
    by_cases h : a = b
    · subst h; simp
    · simp [h]

theorem typ_append (w w' : List (Fin 2)) : typ A (w ++ w') = typ A w * typ A w' :=
  MinIdeal.BRel.ext fun a b => by
    rw [MinIdeal.BRel.mul_apply]
    exact ⟨exists_mid_of_append, fun ⟨c, h1, h2⟩ => one_le_DxN_append h1 h2⟩

theorem typ_pow (w : List (Fin 2)) (m : ℕ) : typ A w ^ m = typ A (List.replicate m w).flatten := by
  induction m with
  | zero => simp [typ_nil]
  | succ m ih => rw [pow_succ', ih, List.replicate_succ, List.flatten_cons, typ_append]

/-- The monoid of types (generated by the support types of `B₀, B₁`; the monoid `\mathcal M` of Section 6). -/
def typMon : Submonoid (MinIdeal.BRel Q) := Submonoid.closure {typ A [0], typ A [1]}

theorem typ_mem (w : List (Fin 2)) : typ A w ∈ typMon A := by
  induction w with
  | nil => rw [typ_nil]; exact (typMon A).one_mem
  | cons b w ih =>
    rw [show b :: w = [b] ++ w from rfl, typ_append]
    refine (typMon A).mul_mem ?_ ih
    apply Submonoid.subset_closure
    fin_cases b
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem exists_typ_of_mem {X : MinIdeal.BRel Q} (hX : X ∈ typMon A) : ∃ w, typ A w = X := by
  induction hX using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨[0], rfl⟩
    · exact ⟨[1], rfl⟩
  | one => exact ⟨[], typ_nil A⟩
  | mul x y _ _ hx hy =>
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨w', rfl⟩ := hy
    exact ⟨w ++ w', typ_append A w w'⟩

/-- **`u*`** (as in Section 6): a word whose type is an idempotent of the minimal ideal of the monoid of types. The index set is all of `Q`. -/
def IsUStar (u : List (Fin 2)) : Prop :=
  ∃ Km : Set (MinIdeal.BRel Q), MinIdeal.IsMinIdeal (typMon A) Km ∧ typ A u ∈ Km ∧ typ A u * typ A u = typ A u

theorem exists_ustar : ∃ u, IsUStar A u := by
  obtain ⟨Km, hK, E, hE, hidem⟩ := MinIdeal.exists_minIdeal_idem (typ A [0]) (typ A [1])
  obtain ⟨u, rfl⟩ := exists_typ_of_mem A (hK.1.2.1 hE)
  exact ⟨u, Km, hK, hE, hidem⟩

/-- **Lemma 10.7** (`u*` kills the components that are not survivable): if a strongly connected component `C` has a word that kills it, then `D^C_{u*} = 0`.
No assumption that the monoid avoids zero is needed (if it contains zero, the minimal ideal is zero and `D^C_{u*} = 0` is trivial). Neither relevance nor internal edges are used. -/
theorem ustar_kills {u : List (Fin 2)} (hu : IsUStar A u) (q : Q) {z : List (Fin 2)}
    (hz : Kills A (sccOf A q) z) : DC A (sccOf A q) u = 0 := by
  obtain ⟨Km, hK, huK, hidem⟩ := hu
  ext ⟨a, ha⟩ ⟨b, hb⟩
  by_contra hne
  have hEab : typ A u a b := by
    show 1 ≤ Rigid.DxN A.B u a b
    rw [← DC_apply A q u ⟨a, ha⟩ ⟨b, hb⟩]
    simp only [Matrix.zero_apply] at hne
    omega
  have hR := MinIdeal.inH_of_minIdeal hK huK hidem (typ_mem A z)
  obtain ⟨m, hm, hpow⟩ := hR.exists_pow_eq hidem
  rw [← typ_append, ← typ_append, typ_pow] at hpow
  have hab : typ A (List.replicate m (u ++ z ++ u)).flatten a b := hpow ▸ hEab
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [List.replicate_succ, List.flatten_cons] at hab
  have hw : u ++ z ++ u ++ (List.replicate m' (u ++ z ++ u)).flatten =
      u ++ (z ++ (u ++ (List.replicate m' (u ++ z ++ u)).flatten)) := by simp
  change 1 ≤ Rigid.DxN A.B _ a b at hab
  rw [hw] at hab
  obtain ⟨x, hax, hxb⟩ := exists_mid_of_append hab
  obtain ⟨y, hxy, hyb⟩ := exists_mid_of_append hxb
  have hxC : x ∈ sccOf A q :=
    sccOf_convex A q a ha b hb x (conn_of_DxN A hax) (conn_of_DxN A hxb)
  have hyC : y ∈ sccOf A q :=
    sccOf_convex A q a ha b hb y (conn_trans A (conn_of_DxN A hax) (conn_of_DxN A hxy)) (conn_of_DxN A hyb)
  have h0 : Rigid.DxN A.B z x y = 0 := by
    rw [← DC_apply A q z ⟨x, hxC⟩ ⟨y, hyC⟩]
    unfold Kills at hz
    rw [hz]; rfl
  omega

/-- If `D^C_u = 0`, then `D^C_w = 0` also for every word `w` that contains `u` as a factor. -/
theorem DC_eq_zero_of_infix {C : Finset Q} {u w : List (Fin 2)} (hu : DC A C u = 0) (h : u <:+: w) :
    DC A C w = 0 := by
  obtain ⟨s, t, rfl⟩ := h
  rw [DC_append, DC_append, hu, mul_zero, zero_mul]

/-- If `D^C_u = 0`, the sum for `π_C(u)` is the sum over all words (`=` the sum of the entries of `A_C^L`). -/
theorem piSum_eq_full {C : Finset Q} {u : List (Fin 2)} (hu : DC A C u = 0) (L : ℕ) :
    piSum A C u L = (esum (AC A C ^ L) : ℝ) := by
  rw [AC, ← wsum_esum]
  refine Rigid.wsum_congr fun w _ => ?_
  split_ifs with h
  · rw [show Rigid.DxN (compMat A C) w = 0 from DC_eq_zero_of_infix A hu h]; simp [esum]
  · rfl

/-- **Second half of Lemma 10.7**: on a strongly connected component that is not survivable, `π_C(u*) < 0 ⟺ ρ(A_C) < 2` for every `u*`
(the sign form of `π_C = log(ρ(A_C)/2)`; independent of `u*`). -/
theorem piNeg_iff_rhoLt {u : List (Fin 2)} (hu : IsUStar A u) (q : Q) (hns : ¬ Survivable A (sccOf A q)) :
    PiNeg A (sccOf A q) u ↔ RhoLt (AC A (sccOf A q)) 2 := by
  obtain ⟨z, hz⟩ := (not_survivable_iff A _).1 hns
  have hu0 := ustar_kills A hu q hz
  rw [← decay2_iff_rhoLt]
  unfold PiNeg Decay2
  simp_rw [piSum_eq_full A hu0]

end Pi

/-! ## §7 The counting for (A^rel): a 0/1 component that is not survivable has `ρ < 2` -/

section Count

variable {K : Type*} [Fintype K] [DecidableEq K]

theorem bsum_mul_left (κ m : ℕ) (c : ℝ) (F : List (List (Fin 2)) → ℝ) :
    Rigid.bsum κ m (fun bs => c * F bs) = c * Rigid.bsum κ m F := by
  induction m generalizing F with
  | zero => rfl
  | succ m ih =>
    simp only [Rigid.bsum]
    simp_rw [ih]
    exact Rigid.wsum_mul_left _ _ _

/-- The indicator of the sequences that avoid the killing word `z`. -/
noncomputable def avoidInd (z : List (Fin 2)) (bs : List (List (Fin 2))) : ℝ :=
  (bs.map (fun b => if b = z then (0 : ℝ) else 1)).prod

theorem wsum_not_eq (z : List (Fin 2)) :
    Rigid.wsum z.length (fun b => if b = z then (0 : ℝ) else 1) = 2 ^ z.length - 1 := by
  have : (fun b : List (Fin 2) => if b = z then (0 : ℝ) else 1) =
      fun b => 1 + (-1) * (if b = z then (1 : ℝ) else 0) := by
    funext b; split_ifs <;> ring
  rw [this, Rigid.wsum_add, Rigid.wsum_const, Rigid.wsum_mul_left, Rigid.wsum_indicator]
  ring

theorem bsum_avoidInd (z : List (Fin 2)) (k : ℕ) :
    Rigid.bsum z.length k (avoidInd z) = (2 ^ z.length - 1) ^ k := by
  induction k with
  | zero => simp [Rigid.bsum, avoidInd]
  | succ k ih =>
    simp only [Rigid.bsum]
    have : ∀ b : List (Fin 2), Rigid.bsum z.length k (fun bs => avoidInd z (b :: bs)) =
        (if b = z then (0 : ℝ) else 1) * (2 ^ z.length - 1) ^ k := by
      intro b
      simp only [avoidInd, List.map_cons, List.prod_cons]
      rw [bsum_mul_left]
      exact congrArg _ ih
    simp_rw [this]
    have h2 : (fun b : List (Fin 2) => (if b = z then (0 : ℝ) else 1) * (2 ^ z.length - 1) ^ k) =
        fun b => (2 ^ z.length - 1) ^ k * (if b = z then (0 : ℝ) else 1) := by
      funext b; ring
    rw [h2, Rigid.wsum_mul_left, wsum_not_eq]
    ring

theorem DxN_flatten (D : Fin 2 → Matrix K K ℕ) :
    ∀ bs : List (List (Fin 2)), Rigid.DxN D bs.flatten = (bs.map (Rigid.DxN D)).prod
  | [] => rfl
  | b :: bs => by rw [List.flatten_cons, DxN_append', DxN_flatten D bs, List.map_cons, List.prod_cons]

theorem esum_le_of_zeroOne {X : Matrix K K ℕ} (h : ∀ x y, X x y ≤ 1) :
    esum X ≤ Fintype.card K * Fintype.card K := by
  unfold esum
  calc ∑ i, ∑ j, X i j ≤ ∑ _i : K, ∑ _j : K, 1 := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = Fintype.card K * Fintype.card K := by simp

/-- **The counting for (A^rel)** (general form): for a pair `D₀, D₁` of matrices over a non-empty index type such that all products of words are 0/1
and some word `z` kills (`D_z = 0`), `ρ(D₀ + D₁) < 2` (in the form `RhoLt`; `ρ ≤ (2^{|z|} - 1)^{1/|z|} < 2`). -/
theorem rhoLt_of_zeroOne_kills [Nonempty K] (D : Fin 2 → Matrix K K ℕ)
    (h01 : ∀ w x y, Rigid.DxN D w x y ≤ 1) {z : List (Fin 2)} (hz : Rigid.DxN D z = 0) :
    RhoLt (D 0 + D 1) 2 := by
  set m := z.length
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      have hz' : z = [] := List.length_eq_zero_iff.1 h
      obtain ⟨x⟩ := (inferInstance : Nonempty K)
      have := congrFun (congrFun hz x) x
      rw [hz'] at this
      simp at this
    · exact h
  set N : ℝ := (Fintype.card K : ℝ) * Fintype.card K
  have hN : 1 ≤ N := by
    have : 1 ≤ Fintype.card K := Fintype.card_pos
    simp only [N]; exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
  -- Upper bound: `esum ((D₀ + D₁)^{k m}) ≤ N (2^m - 1)^k`
  have hbound : ∀ k : ℕ, (esum ((D 0 + D 1) ^ (k * m)) : ℝ) ≤ N * (2 ^ m - 1) ^ k := by
    intro k
    rw [← wsum_esum, Rigid.wsum_mul_eq_bsum, ← bsum_avoidInd z k, ← bsum_mul_left]
    refine Rigid.bsum_mono fun bs _ => ?_
    by_cases hzb : z ∈ bs
    · have h0 : Rigid.DxN D bs.flatten = 0 := by
        rw [DxN_flatten]
        exact List.prod_eq_zero (List.mem_map.2 ⟨z, hzb, hz⟩)
      have hi : avoidInd z bs = 0 := by
        unfold avoidInd
        exact List.prod_eq_zero (List.mem_map.2 ⟨z, hzb, by simp⟩)
      rw [h0, hi]; simp [esum]
    · have hi : avoidInd z bs = 1 := by
        unfold avoidInd
        refine List.prod_eq_one fun x hx => ?_
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
        have : b ≠ z := fun h => hzb (h ▸ hb)
        simp [this]
      rw [hi, mul_one]
      have := esum_le_of_zeroOne (fun x y => h01 bs.flatten x y)
      simp only [N]; exact_mod_cast this
  -- Take `k` large
  have hr0 : (0 : ℝ) ≤ (2 ^ m - 1) / 2 ^ m := by
    have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    exact div_nonneg (by linarith) (by positivity)
  have hr1 : (2 ^ m - 1) / 2 ^ m < (1 : ℝ) := by
    rw [div_lt_one (by positivity)]; linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := 1 / N) (by positivity) hr1
  refine ⟨(n + 1) * m, by nlinarith, ?_⟩
  have hpow : ((2 ^ m - 1) / 2 ^ m : ℝ) ^ (n + 1) < 1 / N :=
    lt_of_le_of_lt (pow_le_pow_of_le_one hr0 hr1.le (by omega)) hn
  have key : N * (2 ^ m - 1) ^ (n + 1) < (2 : ℝ) ^ ((n + 1) * m) := by
    rw [div_pow, div_lt_div_iff₀ (by positivity) (by positivity), one_mul] at hpow
    calc N * (2 ^ m - 1) ^ (n + 1) < (2 ^ m) ^ (n + 1) := by linarith
      _ = (2 : ℝ) ^ ((n + 1) * m) := by rw [← pow_mul, mul_comm]
  have := (hbound (n + 1)).trans_lt key
  exact_mod_cast this

end Count

/-! ## §8 (A^rel) -/

section ARelSec

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (A : ValAuto Q)

/-- **(A^rel)** (a sufficient condition in an earlier, longer argument): for some `u*`, every relevant strongly connected component outside `Q_{\mathrm s}` (survivable and
0/1) (the set `\mathcal Y`: trivial components, components that are not survivable, components of positive rate) has `π_C(u*) < 0`.
In the earlier argument `Q_{\mathrm s}` was "survivable with `Λ_C = 0`", whose components have 0/1 products by an earlier lemma (here it is defined by 0/1). -/
def ARel : Prop :=
  ∃ u, IsUStar A u ∧ ∀ q, Rel A q →
    ¬ (Survivable A (sccOf A q) ∧ ZeroOne A (sccOf A q)) → PiNeg A (sccOf A q) u

/-- **If all components are 0/1, then (A^rel)** (the remark after Corollary 10.9: the step that derives (A^rel) from "all components of `Q'` are 0/1"
of Corollary 10.9 in an earlier assembly of Theorem 9.2 (i)). A 0/1 component that is not survivable has `ρ < 2` by the counting for (A^rel), and a component without internal
edges has `A_C = 0`. Neither depends on `u*`. -/
theorem aRel_of_zeroOne (h : ∀ C, IsComp A C → ZeroOne A C) : ARel A := by
  obtain ⟨u, hu⟩ := exists_ustar A
  refine ⟨u, hu, fun q hq hnZ => ?_⟩
  refine piNeg_of_decay2 A _ u (decay2_of_rhoLt ?_)
  by_cases hE : HasEdge A (sccOf A q)
  · have h01 := h _ ⟨⟨q, hq, rfl⟩, hE⟩
    have hns : ¬ Survivable A (sccOf A q) := fun hs => hnZ ⟨hs, h01⟩
    obtain ⟨z, hz⟩ := (not_survivable_iff A _).1 hns
    have : Nonempty (sccOf A q) := ⟨⟨q, self_mem_sccOf A q⟩⟩
    exact rhoLt_of_zeroOne_kills (compMat A (sccOf A q)) h01 hz
  · have h0 : AC A (sccOf A q) = 0 := by
      ext x y
      simp only [AC, Matrix.add_apply, Matrix.zero_apply, restrictB, Matrix.submatrix_apply]
      have h0' : ∀ b : Fin 2, A.B b x.1 y.1 = 0 := fun b => by
        by_contra hne
        exact hE ⟨x.1, x.2, y.1, y.2, b, Nat.one_le_iff_ne_zero.2 hne⟩
      simp [h0']
    refine ⟨1, le_rfl, ?_⟩
    rw [h0]; simp [esum]

end ARelSec

end Collatz.Arctic.NatQ5
