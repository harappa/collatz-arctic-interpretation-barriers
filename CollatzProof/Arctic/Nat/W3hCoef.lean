/-
# Stationary means of detours, coefficients and degeneration (Definition 12.20 and Lemma 12.22 of the paper)

The coefficients `C_d(conf)`, the effective degree and the degeneration (Lemma 12.22 of the paper) are given, when all components are 0/1, using only
the fields (`κ`, which is χ of the paper, `g`, `labS`) of the decomposition data `DecompData`. The contents of `DecompData` (the explicit form of `κ`, `g`) are not used.
The written proof is Section 12.6 of the paper.

* **Index of an item** `Item := (γ, k, λ)`. The weight of a detour is `ξ_{γ,k,λ}(r, p) = [s_p = labS λ] g_{γ,k,λ}(r, ω_{(p,p+r]})`.
* **Truncated window function** `phi i J` (the sum over `r ∈ [1, J]`, window length `J`, of the form `φ(x, v)` of Definition 12.12) and its stationary mean
  `QJ i J := statMean (muStepB) J (phi i J) e` (on the class of `e`; Definition 12.12).
* **The uniform bound (H$_<$) holds trivially** (Lemma 12.22 (i) of the paper): `QJ i J ≤ Hb` (independent of `J`; `g ≤ c_P (r+1)^{d_P}`, and
  if `g ≠ 0`, the window has a factor of length at least `r/c_W - 1` without `u♯`, whose proportion is exponentially small; `tail_small`).
* **Stationary mean** `Qc i := sup_J QJ i J` (non-decreasing and bounded, `tendsto_QJ`).
* **Degeneration** (Lemma 12.22 (ii) of the paper, `degen`): if `Qc i = 0`, then `g = 0` on every window of range `r ≥ 1` from the state `x = labS λ`
  of the class. Proved by the positivity of `statMean` (`stat_mean_eq_zero`; Lemma 12.14 of the paper).
* **Coefficients** `coef d s := (1/d!) Σ_{deg γ = d} Σ_λ κ(γ, s, λ) Π_k Qc(γ, k, λ_k)` and the value `V0 s` of degree 0.
* **The value for case A** (`aval_eq_V0`; Lemma 12.22 (iii) of the paper): if all coefficients of positive degree of `s_T` are 0, the value of the point is `V0 s_T` (using `t₀ ≥ |u♯|`).
-/
import CollatzProof.Arctic.Nat.W3hSetup
import CollatzProof.Arctic.Nat.W3GapTail

namespace Collatz.Arctic.NatQ5.W3h

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W3c
open Collatz.Arctic.MinIdeal (BRel IsMinIdeal InH)
open Filter Topology

set_option linter.unusedSectionVars false

/-! ## §0 General lemmas -/

section General

/-- If the average of each state over one step under `avg` is at most `H`, so is the stationary mean. -/
theorem mexp_le_of_avg {S' : Type*} (δ : S' → Bool → S') (J : ℕ) (φ : S' → List Bool → ℝ) {H : ℝ}
    (hH : ∀ x, W3d.avg J (φ x) ≤ H) (x : S') (L : ℕ) : W3d.mexp δ J φ x L ≤ L * H := by
  unfold W3d.mexp W3d.wsum
  rw [W3d.avg_sum]
  have hterm : ∀ p ∈ Finset.range L, W3d.avg (L + J) (fun w => φ (Dfa.run δ x (w.take p)) ((w.drop p).take J)) ≤ H := by
    intro p hp
    have hpL := Finset.mem_range.mp hp
    rw [show L + J = p + (L + J - p) by omega, W3d.avg_append]
    have : ∀ a : List Bool, a.length = p →
        W3d.avg (L + J - p) (fun b => φ (Dfa.run δ x ((a ++ b).take p)) (((a ++ b).drop p).take J)) ≤ H := by
      intro a ha
      have e : ∀ b : List Bool, φ (Dfa.run δ x ((a ++ b).take p)) (((a ++ b).drop p).take J) =
          φ (Dfa.run δ x a) (b.take J) := by
        intro b
        rw [List.take_left' ha, List.drop_left' ha]
      simp_rw [e]
      rw [W3d.avg_take (by omega) (φ (Dfa.run δ x a))]
      exact hH _
    have := W3d.avg_mono (n := p) (G := fun a => W3d.avg (L + J - p) (fun b =>
      φ (Dfa.run δ x ((a ++ b).take p)) (((a ++ b).drop p).take J))) (H := fun _ => H) this
    rwa [W3d.avg_const] at this
  calc ∑ p ∈ Finset.range L, W3d.avg (L + J) (fun w => φ (Dfa.run δ x (w.take p)) ((w.drop p).take J))
      ≤ ∑ _p ∈ Finset.range L, H := Finset.sum_le_sum hterm
    _ = L * H := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem statMean_le_of_avg {S' : Type*} [Fintype S'] [DecidableEq S'] {δ : S' → Bool → S'} {J : ℕ}
    {φ : S' → List Bool → ℝ} {q₀ : S'} (hrec : Dfa.Recurrent δ q₀) {C : ℝ} (hC : ∀ x v, |φ x v| ≤ C)
    {H : ℝ} (hH : ∀ x, W3d.avg J (φ x) ≤ H) : W3d.statMean δ J φ q₀ ≤ H := by
  refine le_of_tendsto (W3d.tendsto_statMean J hrec hC) ?_
  filter_upwards [eventually_ge_atTop 1] with L hL
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  rw [div_le_iff₀ hLpos, mul_comm]
  exact mexp_le_of_avg δ J φ hH q₀ L

/-- The factor of length `n` of a word `l` at position `i` is a factor of the factor of length `ℓ` at position `a ≤ i` (`i + n ≤ a + ℓ`). -/
theorem infix_drop_take {α : Type*} (l : List α) {a i n ℓ : ℕ} (hai : a ≤ i) (hin : i + n ≤ a + ℓ) :
    (l.drop i).take n <:+: (l.drop a).take ℓ := by
  have e1 : l.drop i = (l.drop a).drop (i - a) := by rw [List.drop_drop]; congr 1; omega
  have e2 : ((l.drop a).drop (i - a)).take n = (((l.drop a).take ℓ).drop (i - a)).take n := by
    rw [List.drop_take, List.take_take]
    congr 1
    omega
  rw [e1, e2]
  exact (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix

/-- A shorter part of a part without `u♯` has no `u♯` either. -/
theorem not_infix_take_le {us w : List (Fin 2)} {ℓ₀ ℓ : ℕ} (h : ℓ₀ ≤ ℓ) (hw : ¬ us <:+: w.take ℓ) :
    ¬ us <:+: w.take ℓ₀ := by
  intro hc
  apply hw
  refine hc.trans ?_
  have : w.take ℓ₀ = (w.take ℓ).take ℓ₀ := by rw [List.take_take, Nat.min_eq_left h]
  rw [this]
  exact (List.take_prefix _ _).isInfix

theorem l2f_bitLetter (b : Fin 2) : W3a.l2f (bitLetter b) = b := by fin_cases b <;> rfl

theorem map_l2f_bitLetter (w : List (Fin 2)) : (w.map bitLetter).map W3a.l2f = w := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id w]
  exact List.map_congr_left (fun b _ => l2f_bitLetter b)

theorem bitLetter_mem_wordsOfLen (w : List (Fin 2)) : w.map bitLetter ∈ wordsOfLen (w.map bitLetter).length := by
  refine mem_wordsOfLen_of rfl ?_
  intro s hs
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hs
  unfold bitLetter; split_ifs <;> simp

/-- If the interval `[a, a+ℓ)` of the image under `l2f` of a word `w` (of letters) does not contain `u♯`, no window in the interval is `u♯`. -/
theorem window_ne_of_not_infix {w : Word} {us : List (Fin 2)} {a ℓ : ℕ}
    (h : ¬ us <:+: ((w.map W3a.l2f).drop a).take ℓ) :
    ∀ i, a ≤ i → i + (us.map bitLetter).length ≤ a + ℓ →
      window w i (us.map bitLetter).length ≠ us.map bitLetter := by
  intro i hai hin hwin
  apply h
  rw [List.length_map] at hin
  have hsub := infix_drop_take (w.map W3a.l2f) hai hin
  have e : ((w.map W3a.l2f).drop i).take us.length = us := by
    have hw' : (w.drop i).take us.length = us.map bitLetter := by
      have := hwin; unfold window at this; rwa [List.length_map] at this
    rw [← List.map_drop, ← List.map_take, hw', map_l2f_bitLetter]
  rwa [e] at hsub

theorem map_toB_map_b2f (w : Word) : (w.map W3d.toB).map W3d.b2f = w.map W3a.l2f := by
  rw [List.map_map]
  refine List.map_congr_left (fun s _ => ?_)
  simp only [Function.comp_apply, W3d.toB, W3d.b2f, W3a.l2f]
  by_cases h : s = Letter.t <;> simp [h]

theorem ofFn_map_l2f {r : ℕ} (g : Fin r → Bool) :
    (List.ofFn (fun i => if g i then Letter.t else Letter.f)).map W3a.l2f = (List.ofFn g).map W3d.b2f := by
  simp only [List.map_ofFn]
  congr 1
  funext i
  by_cases h : g i <;> simp [h, W3a.l2f, W3d.b2f]

theorem ofFn_letter_injective (r : ℕ) :
    Function.Injective (fun g : Fin r → Bool => (List.ofFn (fun i => if g i then Letter.t else Letter.f) : Word)) := by
  intro g g' hgg
  funext i
  have := congrArg (fun l => l[i.val]?) hgg
  simp only [List.getElem?_ofFn] at this
  by_cases h1 : g i <;> by_cases h2 : g' i <;> simp_all

/-- The positions `[a, a+ℓ)` of a word `l` do not contain `u♯` (wrapped in a definition to avoid a mismatch of `DecidablePred` instances). -/
def FreeW (us : List (Fin 2)) (a ℓ : ℕ) (l : List (Fin 2)) : Prop := ¬ us <:+: (l.drop a).take ℓ

/-- The part of length `ℓ` of a word `l` from some position `a < A` does not contain `u♯`. -/
def BadW (us : List (Fin 2)) (ℓ A : ℕ) (l : List (Fin 2)) : Prop := ∃ a, a < A ∧ FreeW us a ℓ l

open Classical in
theorem card_noOcc_fin (us : List (Fin 2)) {r a ℓ : ℕ} (h : a + ℓ ≤ r) :
    (((Finset.univ : Finset (Fin r → Bool)).filter
        (fun g => FreeW us a ℓ ((List.ofFn g).map W3d.b2f))).card : ℝ) ≤
      2 ^ r * (1 - 1 / 2 ^ us.length) ^ (ℓ / us.length) := by
  have hle : ((Finset.univ : Finset (Fin r → Bool)).filter
        (fun g => FreeW us a ℓ ((List.ofFn g).map W3d.b2f))).card ≤
      ((wordsOfLen r).filter (fun w => ∀ i, a ≤ i → i + (us.map bitLetter).length ≤ a + ℓ →
        window w i (us.map bitLetter).length ≠ us.map bitLetter)).card := by
    refine Finset.card_le_card_of_injOn (fun g : Fin r → Bool => (List.ofFn (fun i => if g i then Letter.t else Letter.f) : Word))
      (fun g hg => ?_) ((ofFn_letter_injective r).injOn)
    rw [Finset.mem_coe, Finset.mem_filter] at hg
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩, ?_⟩
    have : FreeW us a ℓ ((List.ofFn g).map W3d.b2f) := hg.2
    unfold FreeW at this
    rw [← ofFn_map_l2f] at this
    exact window_ne_of_not_infix this
  have hc := card_noOcc_le r a (a + ℓ) (bitLetter_mem_wordsOfLen us) h
  have hcR := (Rat.cast_le (K := ℝ)).mpr hc
  push_cast at hcR
  calc _ ≤ (((wordsOfLen r).filter (fun w => ∀ i, a ≤ i → i + (us.map bitLetter).length ≤ a + ℓ →
        window w i (us.map bitLetter).length ≠ us.map bitLetter)).card : ℝ) := by exact_mod_cast hle
    _ ≤ _ := hcR
    _ = _ := by rw [List.length_map, Nat.add_sub_cancel_left]

end General

/-! ## §1 Indices of items and window functions -/

namespace Setup

variable {Q : Type} [Fintype Q] [DecidableEq Q] {B : ValAuto Q} (S : Setup B)

/-- The index `(γ, k, λ)` of an item. -/
abbrev Item := Σ γ : S.D.Γ, Fin (S.D.deg γ) × S.D.Lab

/-- The weight function `g_{γ,k,λ}` of the detour of an item. -/
def gI (i : S.Item) : ℕ → List (Fin 2) → ℕ := S.D.g i.1 i.2.1 i.2.2

/-- The forward state of the label of an item. -/
def labI (i : S.Item) : BRel (ZIdx B) := S.D.labS i.2.2

/-- The sum of the weights of detours over the ranges `r ∈ [1, J]`, as a function of a state and a window of length `J` (`Bool`) (natural numbers). -/
noncomputable def phiN (i : S.Item) (J : ℕ) (x : BRel (ZIdx B)) (v : List Bool) : ℕ :=
  ind (x = S.labI i) * ∑ r ∈ Finset.Icc 1 J, S.gI i r ((v.map W3d.b2f).take r)

/-- The real value (`φ` of Definition 12.12). -/
noncomputable def phi (i : S.Item) (J : ℕ) (x : BRel (ZIdx B)) (v : List Bool) : ℝ := (S.phiN i J x v : ℝ)

/-- The truncation bound `B_J := Σ_{r ≤ J} c_P (r+1)^{d_P}`. -/
def BJ (J : ℕ) : ℕ := ∑ r ∈ Finset.Icc 1 J, S.D.cP * (r + 1) ^ S.D.dP

theorem phiN_le (i : S.Item) (J : ℕ) (x : BRel (ZIdx B)) (v : List Bool) : S.phiN i J x v ≤ S.BJ J := by
  unfold phiN BJ
  calc ind (x = S.labI i) * ∑ r ∈ Finset.Icc 1 J, S.gI i r ((v.map W3d.b2f).take r)
      ≤ 1 * ∑ r ∈ Finset.Icc 1 J, S.gI i r ((v.map W3d.b2f).take r) := Nat.mul_le_mul_right _ (ind_le_one _)
    _ = ∑ r ∈ Finset.Icc 1 J, S.gI i r ((v.map W3d.b2f).take r) := one_mul _
    _ ≤ _ := Finset.sum_le_sum (fun r _ => S.D.g_poly _ _ _ _ _)

theorem abs_phi_le (i : S.Item) (J : ℕ) (x : BRel (ZIdx B)) (v : List Bool) : |S.phi i J x v| ≤ S.BJ J := by
  unfold phi
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast S.phiN_le i J x v

theorem phi_nonneg (i : S.Item) (J : ℕ) (x : BRel (ZIdx B)) (v : List Bool) : 0 ≤ S.phi i J x v :=
  Nat.cast_nonneg _

/-- `e` is a recurrent state of the DFA of forward states. -/
theorem e_recurrent : Dfa.Recurrent (muStepB B) S.e := muStepB_recurrent B S.hS.minIdeal S.hS.mem

/-- The truncated stationary mean `Q_J`. -/
noncomputable def QJ (i : S.Item) (J : ℕ) : ℝ := W3d.statMean (muStepB B) J (S.phi i J) S.e

theorem QJ_nonneg (i : S.Item) (J : ℕ) : 0 ≤ S.QJ i J :=
  W3d.statMean_nonneg J S.e_recurrent (S.abs_phi_le i J) (fun x v _ _ => S.phi_nonneg i J x v)

theorem QJ_le_succ (i : S.Item) (J : ℕ) : S.QJ i J ≤ S.QJ i (J + 1) := by
  unfold QJ
  rw [← W3d.statMean_take (J := J) (J' := J + 1) (Nat.le_succ J) S.e]
  refine W3d.statMean_mono (J + 1) S.e_recurrent (C := S.BJ J) (D := S.BJ (J + 1))
    (fun x v => S.abs_phi_le i J x (v.take J)) (S.abs_phi_le i (J + 1)) (fun x v _ hv => ?_)
  unfold phi
  apply Nat.cast_le.mpr
  unfold phiN
  apply Nat.mul_le_mul_left
  have e : ∀ r ∈ Finset.Icc 1 J, S.gI i r (((v.take J).map W3d.b2f).take r) =
      S.gI i r ((v.map W3d.b2f).take r) := by
    intro r hr
    rw [List.map_take, List.take_take, Nat.min_eq_left (Finset.mem_Icc.mp hr).2]
  rw [Finset.sum_congr rfl e]
  exact Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc le_rfl (Nat.le_succ J))

theorem QJ_mono (i : S.Item) : Monotone (S.QJ i) := monotone_nat_of_le_succ (S.QJ_le_succ i)

/-! ## §2 (H$_<$): a uniform bound for the truncated stationary means -/

/-- A positive version of `c_W`. -/
def cW' : ℕ := max S.D.cW 1

/-- The lower bound `ℓ₀(r) = ⌊r/c_W'⌋ - 1` for the length of the part without `u♯` needed in a window of range `r`. -/
def ell0 (r : ℕ) : ℕ := r / S.cW' - 1

theorem cW'_pos : 1 ≤ S.cW' := le_max_right _ _

/-- If `g ≠ 0`, the part of length `ℓ₀` from a position `a` of the window (`a + ℓ₀ ≤ r`) does not contain `u♯`. -/
theorem free_of_g_ne (i : S.Item) {r : ℕ} {v : List (Fin 2)} (hg : S.gI i r v ≠ 0) :
    ∃ a, a + S.ell0 r ≤ r ∧ ¬ S.us <:+: (v.drop a).take (S.ell0 r) := by
  obtain ⟨a, ℓ, hal, hrl, hfree⟩ := S.D.g_free i.1 i.2.1 i.2.2 r v hg
  have hℓ : S.ell0 r ≤ ℓ := by
    unfold ell0
    have h1 : r ≤ S.cW' * (ℓ + 1) := le_trans hrl (Nat.mul_le_mul_right _ (le_max_left _ _))
    have h2 : r / S.cW' ≤ ℓ + 1 := by
      rw [Nat.div_le_iff_le_mul_add_pred (by have := S.cW'_pos; omega)]
      nlinarith [S.cW'_pos]
    omega
  exact ⟨a, by omega, not_infix_take_le hℓ hfree⟩

/-- An upper bound for the average weight of the detours of range `r` (a real number). -/
noncomputable def bnd (r : ℕ) : ℚ :=
  S.D.cP * ((r : ℚ) + 1) ^ S.D.dP * ((r + 1) * (1 - 1 / 2 ^ S.us.length) ^ (S.ell0 r / S.us.length))

theorem bnd_nonneg (r : ℕ) : 0 ≤ S.bnd r := by
  unfold bnd
  have : (0 : ℚ) ≤ 1 - 1 / 2 ^ S.us.length := by
    rw [sub_nonneg, div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  positivity

open Classical in
/-- The uniform average of the weight of range `r` is at most `bnd r`. -/
theorem avg_g_le (i : S.Item) (r : ℕ) :
    W3d.avg r (fun v => (S.gI i r (v.map W3d.b2f) : ℝ)) ≤ (S.bnd r : ℝ) := by
  have hq0 : (0 : ℝ) ≤ 1 - 1 / 2 ^ S.us.length := by
    rw [sub_nonneg, div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  set c : ℝ := S.D.cP * ((r : ℝ) + 1) ^ S.D.dP with hc
  have hc0 : 0 ≤ c := by positivity
  have h1 : ∑ g : Fin r → Bool, (S.gI i r ((List.ofFn g).map W3d.b2f) : ℝ) =
      ∑ g ∈ (Finset.univ : Finset (Fin r → Bool)).filter
        (fun g => BadW S.us (S.ell0 r) (r - S.ell0 r + 1) ((List.ofFn g).map W3d.b2f)),
        (S.gI i r ((List.ofFn g).map W3d.b2f) : ℝ) := by
    refine (Finset.sum_filter_of_ne (fun g _ hg => ?_)).symm
    have hg' : S.gI i r ((List.ofFn g).map W3d.b2f) ≠ 0 := by exact_mod_cast hg
    obtain ⟨a, ha, hfree⟩ := S.free_of_g_ne i hg'
    exact ⟨a, by omega, hfree⟩
  have h2 : ∑ g ∈ (Finset.univ : Finset (Fin r → Bool)).filter
        (fun g => BadW S.us (S.ell0 r) (r - S.ell0 r + 1) ((List.ofFn g).map W3d.b2f)),
        (S.gI i r ((List.ofFn g).map W3d.b2f) : ℝ) ≤
      ((Finset.univ : Finset (Fin r → Bool)).filter
        (fun g => BadW S.us (S.ell0 r) (r - S.ell0 r + 1) ((List.ofFn g).map W3d.b2f))).card * c := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum (fun g _ => ?_)
    have := S.D.g_poly i.1 i.2.1 i.2.2 r ((List.ofFn g).map W3d.b2f)
    simp only [hc]
    exact_mod_cast this
  have hℓ : S.ell0 r ≤ r := by unfold ell0; have := Nat.div_le_self r S.cW'; omega
  have h3 : (((Finset.univ : Finset (Fin r → Bool)).filter
        (fun g => BadW S.us (S.ell0 r) (r - S.ell0 r + 1) ((List.ofFn g).map W3d.b2f))).card : ℝ) ≤
      (r + 1) * (2 ^ r * (1 - 1 / 2 ^ S.us.length) ^ (S.ell0 r / S.us.length)) := by
    have hsub : (Finset.univ : Finset (Fin r → Bool)).filter
        (fun g => BadW S.us (S.ell0 r) (r - S.ell0 r + 1) ((List.ofFn g).map W3d.b2f)) ⊆
        (Finset.range (r - S.ell0 r + 1)).biUnion (fun a => (Finset.univ : Finset (Fin r → Bool)).filter
          (fun g => FreeW S.us a (S.ell0 r) ((List.ofFn g).map W3d.b2f))) := by
      intro g hg
      rw [Finset.mem_filter] at hg
      obtain ⟨a, ha, hfree⟩ := hg.2
      exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_range.mpr ha, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfree⟩⟩
    have hle := le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
    calc _ ≤ ((∑ a ∈ Finset.range (r - S.ell0 r + 1), ((Finset.univ : Finset (Fin r → Bool)).filter
            (fun g => FreeW S.us a (S.ell0 r) ((List.ofFn g).map W3d.b2f))).card : ℕ) : ℝ) := by
          exact_mod_cast hle
      _ = ∑ a ∈ Finset.range (r - S.ell0 r + 1), (((Finset.univ : Finset (Fin r → Bool)).filter
            (fun g => FreeW S.us a (S.ell0 r) ((List.ofFn g).map W3d.b2f))).card : ℝ) := by
          push_cast; rfl
      _ ≤ ∑ _a ∈ Finset.range (r - S.ell0 r + 1), 2 ^ r * (1 - 1 / 2 ^ S.us.length) ^ (S.ell0 r / S.us.length) := by
          refine Finset.sum_le_sum (fun a ha => ?_)
          have := Finset.mem_range.mp ha
          exact card_noOcc_fin S.us (by omega)
      _ = ((r - S.ell0 r + 1 : ℕ) : ℝ) * (2 ^ r * (1 - 1 / 2 ^ S.us.length) ^ (S.ell0 r / S.us.length)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (r + 1) * (2 ^ r * (1 - 1 / 2 ^ S.us.length) ^ (S.ell0 r / S.us.length)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : r - S.ell0 r + 1 ≤ r + 1 := by omega
          exact_mod_cast this
  unfold W3d.avg
  rw [h1, div_le_iff₀ (by positivity)]
  unfold bnd
  push_cast
  calc _ ≤ _ := h2
    _ ≤ (r + 1) * (2 ^ r * (1 - 1 / 2 ^ S.us.length) ^ (S.ell0 r / S.us.length)) * c :=
        mul_le_mul_of_nonneg_right h3 hc0
    _ = _ := by simp only [hc]; ring

/-- The uniform average of the window function is at most `Σ_{r ≤ J} bnd r`. -/
theorem avg_phi_le (i : S.Item) (J : ℕ) (x : BRel (ZIdx B)) :
    W3d.avg J (S.phi i J x) ≤ ∑ r ∈ Finset.Icc 1 J, (S.bnd r : ℝ) := by
  have hpt : ∀ v : List Bool, v.length = J → S.phi i J x v ≤
      ∑ r ∈ Finset.Icc 1 J, (S.gI i r ((v.map W3d.b2f).take r) : ℝ) := by
    intro v _
    unfold phi phiN
    push_cast
    have h1 : ((ind (x = S.labI i) : ℕ) : ℝ) ≤ 1 := by exact_mod_cast ind_le_one _
    have h2 : (0 : ℝ) ≤ ∑ r ∈ Finset.Icc 1 J, (S.gI i r ((v.map W3d.b2f).take r) : ℝ) :=
      Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    nlinarith
  refine le_trans (W3d.avg_mono hpt) ?_
  rw [W3d.avg_sum]
  refine Finset.sum_le_sum (fun r hr => ?_)
  have hrJ := (Finset.mem_Icc.mp hr).2
  have e : ∀ v : List Bool, (S.gI i r ((v.map W3d.b2f).take r) : ℝ) =
      (fun w : List Bool => (S.gI i r (w.map W3d.b2f) : ℝ)) (v.take r) := by
    intro v; simp only [List.map_take]
  simp_rw [e]
  rw [W3d.avg_take hrJ (fun w : List Bool => (S.gI i r (w.map W3d.b2f) : ℝ))]
  exact S.avg_g_le i r

/-- **A uniform bound for (H$_<$)**: `Σ_{r ≤ J} bnd r ≤ Hb` for some `Hb` independent of `J`. -/
theorem exists_Hb : ∃ Hb : ℝ, 0 ≤ Hb ∧ ∀ J, ∑ r ∈ Finset.Icc 1 J, (S.bnd r : ℝ) ≤ Hb := by
  have hus := S.us_length_pos
  have hcW := S.cW'_pos
  have hq0 : (0 : ℚ) ≤ 1 - 1 / 2 ^ S.us.length := by
    rw [sub_nonneg, div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hq1 : (1 : ℚ) - 1 / 2 ^ S.us.length < 1 := by
    have : (0 : ℚ) < 1 / 2 ^ S.us.length := by positivity
    linarith
  obtain ⟨J₁, hJ₁⟩ := W3b.tail_small (S.D.cP : ℚ) (Nat.cast_nonneg _) S.D.dP 1 0 zero_le_one le_rfl
    (S.cW' * S.us.length) (S.cW' * S.us.length + 2 * S.cW') (Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega)))
    (1 - 1 / 2 ^ S.us.length) hq0 hq1 (fun R => R) (fun R => S.ell0 R / S.us.length)
    (fun R => by simp) (fun R => by
      -- `R ≤ c_W' |u♯| ⌊ℓ₀/|u♯|⌋ + c_W' |u♯| + 2 c_W'`
      unfold ell0
      have h1 := Nat.lt_mul_div_succ R (show 0 < S.cW' by omega)
      have h2 := Nat.lt_mul_div_succ (R / S.cW' - 1) hus
      generalize R / S.cW' = q at h1 h2 ⊢
      generalize (q - 1) / S.us.length = Kq at h2 ⊢
      rw [Nat.mul_succ] at h1 h2
      have hq : q ≤ S.us.length * Kq + S.us.length := by omega
      have h3 : S.cW' * q ≤ S.cW' * (S.us.length * Kq + S.us.length) := Nat.mul_le_mul_left _ hq
      rw [Nat.mul_add, ← Nat.mul_assoc] at h3
      omega) 1 one_pos
  refine ⟨∑ r ∈ Finset.range (J₁ + 1), (S.bnd r : ℝ) + 1, by
    have := Finset.sum_nonneg (fun r (_ : r ∈ Finset.range (J₁ + 1)) => (by exact_mod_cast S.bnd_nonneg r : (0 : ℝ) ≤ S.bnd r))
    linarith, fun J => ?_⟩
  have htail := hJ₁ ((Finset.Icc 1 J).filter (fun r => J₁ < r)) (fun R hR => (Finset.mem_filter.mp hR).2)
  have htail' : ∑ r ∈ (Finset.Icc 1 J).filter (fun r => J₁ < r), (S.bnd r : ℝ) ≤ 1 := by
    have e : ∀ r, S.bnd r = (S.D.cP : ℚ) * ((r : ℚ) + 1) ^ S.D.dP * (((r : ℕ) + 1 : ℚ) *
        (1 - 1 / 2 ^ S.us.length) ^ (S.ell0 r / S.us.length)) := fun r => rfl
    have : ∑ r ∈ (Finset.Icc 1 J).filter (fun r => J₁ < r), S.bnd r ≤ 1 := by
      simp only [e]; exact htail
    exact_mod_cast this
  have hhead : ∑ r ∈ (Finset.Icc 1 J).filter (fun r => ¬ J₁ < r), (S.bnd r : ℝ) ≤
      ∑ r ∈ Finset.range (J₁ + 1), (S.bnd r : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun r hr => ?_) (fun r _ _ => by exact_mod_cast S.bnd_nonneg r)
    rw [Finset.mem_filter] at hr
    exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 J) (fun r => J₁ < r)]
  linarith

/-- The value of the uniform bound. -/
noncomputable def Hb : ℝ := Classical.choose S.exists_Hb

theorem Hb_nonneg : 0 ≤ S.Hb := (Classical.choose_spec S.exists_Hb).1

theorem sum_bnd_le_Hb (J : ℕ) : ∑ r ∈ Finset.Icc 1 J, (S.bnd r : ℝ) ≤ S.Hb := (Classical.choose_spec S.exists_Hb).2 J

theorem QJ_le_Hb (i : S.Item) (J : ℕ) : S.QJ i J ≤ S.Hb :=
  statMean_le_of_avg S.e_recurrent (S.abs_phi_le i J) (fun x => le_trans (S.avg_phi_le i J x) (S.sum_bnd_le_Hb J))

theorem bdd_QJ (i : S.Item) : BddAbove (Set.range (S.QJ i)) := ⟨S.Hb, by rintro _ ⟨J, rfl⟩; exact S.QJ_le_Hb i J⟩

/-! ## §3 Stationary means and degeneration -/

/-- **The stationary mean of a detour** `Q(ξ_{γ,k,λ}) := sup_J Q_J`. -/
noncomputable def Qc (i : S.Item) : ℝ := ⨆ J, S.QJ i J

theorem QJ_le_Qc (i : S.Item) (J : ℕ) : S.QJ i J ≤ S.Qc i := le_ciSup (S.bdd_QJ i) J

theorem Qc_nonneg (i : S.Item) : 0 ≤ S.Qc i := le_trans (S.QJ_nonneg i 0) (S.QJ_le_Qc i 0)

theorem Qc_le_Hb (i : S.Item) : S.Qc i ≤ S.Hb := ciSup_le (S.QJ_le_Hb i)

theorem tendsto_QJ (i : S.Item) : Tendsto (S.QJ i) atTop (𝓝 (S.Qc i)) :=
  tendsto_atTop_ciSup (S.QJ_mono i) (S.bdd_QJ i)

/-- **Degeneration** (Lemma 12.22 (ii) of the paper): if `Q = 0`, then `g = 0` on every window of range `r ≥ 1` from the state `x = labS λ` of the class. -/
theorem degen (i : S.Item) (h0 : S.Qc i = 0) {x : BRel (ZIdx B)} (hx : Dfa.Reach (muStepB B) S.e x)
    (hlab : x = S.labI i) {r : ℕ} (hr : 1 ≤ r) (v : List (Fin 2)) (hv : v.length = r) : S.gI i r v = 0 := by
  have hQ : S.QJ i r = 0 := le_antisymm (h0 ▸ S.QJ_le_Qc i r) (S.QJ_nonneg i r)
  have hφ := (W3d.stat_mean_eq_zero r S.e_recurrent (S.abs_phi_le i r)
    (fun x v _ _ => S.phi_nonneg i r x v)).1 hQ x (v.map W3d.f2b) hx (by rw [List.length_map, hv])
  unfold phi at hφ
  have hN : S.phiN i r x (v.map W3d.f2b) = 0 := by exact_mod_cast hφ
  unfold phiN at hN
  have hind : ind (x = S.labI i) = 1 := by unfold ind; simp [hlab]
  rw [hind, one_mul, Finset.sum_eq_zero_iff] at hN
  have := hN r (Finset.mem_Icc.mpr ⟨hr, le_rfl⟩)
  have e : ((v.map W3d.f2b).map W3d.b2f).take r = v := by
    rw [List.map_map]
    have : (W3d.b2f ∘ W3d.f2b) = id := funext W3d.b2f_f2b
    rw [this, List.map_id, List.take_of_length_le (by omega)]
  rwa [e] at this

/-! ## §4 Coefficients -/

/-- **Coefficients** `C_d(s) := (1/d!) Σ_{deg γ = d} Σ_λ κ(γ, s, λ) Π_k Q(γ, k, λ_k)`. -/
noncomputable def coef (d : ℕ) (s : BRel (ZIdx B)) : ℝ :=
  (∑ γ ∈ Finset.univ.filter (fun γ => S.D.deg γ = d), ∑ l : Fin (S.D.deg γ) → S.D.Lab,
    (S.D.κ γ s l : ℝ) * ∏ k, S.Qc ⟨γ, k, l k⟩) / (d.factorial : ℝ)

theorem coef_nonneg (d : ℕ) (s : BRel (ZIdx B)) : 0 ≤ S.coef d s := by
  unfold coef
  refine div_nonneg (Finset.sum_nonneg fun γ _ => Finset.sum_nonneg fun l _ =>
    mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun k _ => S.Qc_nonneg _)) (Nat.cast_nonneg _)

/-- If a coefficient is 0, then for each `(γ, λ)` of that degree `κ = 0` or `Q = 0` for some `k`. -/
theorem coef_zero_cases {d : ℕ} {s : BRel (ZIdx B)} (h : S.coef d s = 0) (γ : S.D.Γ) (hγ : S.D.deg γ = d)
    (l : Fin (S.D.deg γ) → S.D.Lab) : S.D.κ γ s l = 0 ∨ ∃ k, S.Qc ⟨γ, k, l k⟩ = 0 := by
  unfold coef at h
  have hf : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · rw [Finset.sum_eq_zero_iff_of_nonneg (fun γ _ => Finset.sum_nonneg fun l _ =>
      mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun k _ => S.Qc_nonneg _))] at h
    have h1 := h γ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hγ⟩)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun l _ =>
      mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun k _ => S.Qc_nonneg _))] at h1
    have h2 := h1 l (Finset.mem_univ _)
    rcases mul_eq_zero.mp h2 with h3 | h3
    · left; exact_mod_cast h3
    · right
      obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp h3
      exact ⟨k, hk⟩
  · exact absurd h hf.ne'

/-- The value of degree 0, `V0 s := Σ_{deg γ = 0} κ(γ, s, ∅)`. -/
noncomputable def V0 (s : BRel (ZIdx B)) : ℕ :=
  ∑ γ, if h : S.D.deg γ = 0 then S.D.κ γ s (fun k => absurd k.2 (by omega)) else 0

/-! ## §5 The value for case A: if the coefficients of positive degree are 0, the value is `V0` -/

/-- The forward state at a position `p ≥ |u♯|` of a point word lies in the class of `e`. -/
theorem reach_of_ge (m : List (Fin 2)) {p : ℕ} (hp : S.us.length ≤ p) :
    Dfa.Reach (muStepB B) S.e (muZ B ((fullW S.us [] S.y'' S.z m S.R).take p)) := by
  have hR : S.τ = S.us ++ (List.replicate (S.R - 1) S.us).flatten := by
    unfold τ
    obtain ⟨R', hR'⟩ : ∃ R', S.R = R' + 1 := ⟨S.R - 1, by have := S.hR1; omega⟩
    rw [hR', List.replicate_succ, List.flatten_cons, Nat.add_sub_cancel]
  set ω := fullW S.us [] S.y'' S.z m S.R
  have hω : ω = S.us ++ ((List.replicate (S.R - 1) S.us).flatten ++ m ++ (S.y'' ++ S.τ ++ S.z)) := by
    simp only [ω, S.fullW_eq, hR, List.append_assoc]
  set rest := (List.replicate (S.R - 1) S.us).flatten ++ m ++ (S.y'' ++ S.τ ++ S.z)
  have htake : ω.take p = S.us ++ rest.take (p - S.us.length) := by
    rw [hω, List.take_append, List.take_of_length_le hp]
  refine ⟨(rest.take (p - S.us.length)).map W3d.f2b, ?_⟩
  have := run_muStepB B S.e (rest.take (p - S.us.length))
  exact this.trans (by rw [htake, muZ_append, S.hS.mu_eq])

open Classical in
/-- **The value for case A** (Lemma 12.22 (iii) of the paper): if all coefficients of positive degree of the forward state `s_T` of the configuration are 0,
the value of the point is `V0 s_T` (using `t₀ ≥ |u♯|` (`hD`) and the degeneration `degen`). -/
theorem aval_eq_V0 (m : List (Fin 2)) (hc : ∀ d, 1 ≤ d → S.coef d (S.D.sT m) = 0) :
    aval B (fullW S.us [] S.y'' S.z m S.R) = S.V0 (S.D.sT m) := by
  rw [S.D.aval_eq_deg0 m (fun γ hγ => ?_)]
  · unfold V0
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    split_ifs with h
    · rw [S.D.term_of_deg_zero m γ h]
    · rfl
  · -- the terms of positive degree are 0
    unfold DecompData.term termOf
    refine Finset.sum_eq_zero (fun l _ => ?_)
    rcases S.coef_zero_cases (hc (S.D.deg γ) (by omega)) γ rfl l with hk | ⟨k, hk⟩
    · rw [DecompData.sT] at hk; rw [hk, zero_mul]
    · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun pr hpr => ?_))
      refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
      unfold admSet at hpr
      rw [Finset.mem_filter] at hpr
      have hadm := hpr.2
      have hp0 : S.D.t0 γ ≤ pr.1 k := adm_ge hadm k
      have hr1 : 1 ≤ pr.2 k := hadm.1 k
      unfold xiOf
      by_cases hlab : muZ B ((fullW S.us [] S.y'' S.z m S.R).take (pr.1 k)) = S.D.labS (l k)
      · have hreach := S.reach_of_ge m (le_trans (S.hD γ) hp0)
        by_cases hlen : (((fullW S.us [] S.y'' S.z m S.R).drop (pr.1 k)).take (pr.2 k)).length = pr.2 k
        · have := S.degen ⟨γ, k, l k⟩ hk hreach hlab hr1 _ hlen
          simp only [gI] at this
          rw [this, mul_zero]
        · have : S.D.g γ k (l k) (pr.2 k) (((fullW S.us [] S.y'' S.z m S.R).drop (pr.1 k)).take (pr.2 k)) = 0 := by
            by_contra hne
            exact hlen (S.D.g_len γ k (l k) _ _ hne)
          rw [this, mul_zero]
      · unfold ind; simp [hlab]

end Setup

end Collatz.Arctic.NatQ5.W3h
