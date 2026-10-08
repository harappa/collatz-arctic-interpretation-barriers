/-
# The setting, the set of configurations and the word of the starting point (Definition 12.20 and Lemma 12.21 of the paper)

The first steps of the order of quantifiers of the proof (automaton → $Q_{\mathrm s}$, $\mathcal M_{\mathrm s}$, $\mathcal K_{\mathrm s}$, `e`, `u♯` → `R` → `σ₀` →
decomposition data) are collected in the structure `Setup`; the set `𝔎` of configurations and the form of the word of the starting point `x₀`
are given. The written proof is Section 12.6 of the paper.

* **`Setup`**: an automaton `B` all of whose components are 0/1, `Sharp B K u♯ e`, `R ≥ |Q|`, the prefix `β₀` (the word of `r_{σ₀}` is
  `y''(u♯)^R z`), decomposition data `D` (`τ' = []`) and **`t₀ ≥ |u♯|`** (`hD`; a lower bound that is not in the frozen statement `DecompData`,
  and holds for the construction of Proposition 12.11, where `t₀` is the end of the unbroken copy of the top `(u♯)^R`).
* **Top window** `τ := (u♯)^R` (the top word $w_{\mathrm{top}}$ of the paper), `E := |τ|` ($L_\tau$), `K := E + 9`, `T₀ := 1τ0^8` (`topT0`; the integer τ of the paper).
* **Configuration** `conf m`: the state of the configuration automaton (forward state and residue) at time `T` of the point word `τ m y''(u♯)^R z`.
  `(conf m).1 = s_T` (`conf_fst`); the residue of the point is `endRes (conf m)` (`valW_res`).
* **Set of configurations** `Kset`: the states reachable from `P₀ := (e, r_τ)` whose forward state satisfies `s e = s` and whose end residue is non-zero
  ($\mathfrak K$ of the paper; the configuration of a point with `3 ∤ x` lies in it: `conf_mem`). It is non-empty (`Kset_nonempty`).
* **Word of the starting point** (`binWord_x0`): `binWord x₀ = τ · (0^8 · u · ρ · r') · y''(u♯)^R z`.
* **Event (c)** (`eventC`): there is `L` such that for every configuration `c` of `𝔎` and every word `w` of `σ` there is a target state `b`, and
  if the length `F ≥ L` of the free bits matches the class `cls b`, then the configuration of `x₀` is `c` for at least `2^{F-L}` values `u`.
* **Choice of `β₀`** (`exists_beta0`): for every word there is `β₀` whose word of `r_{σ₀}` contains it (window frequencies, `hTerrasWin`).
-/
import CollatzProof.Arctic.Nat.W3hConf
import CollatzProof.Arctic.Nat.W3Top

namespace Collatz.Arctic.NatQ5.W3h

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W3c
open Collatz.Arctic.MinIdeal (BRel IsMinIdeal InH)
open Classical

set_option linter.unusedSectionVars false

/-! ## §0 Auxiliary lemmas -/

theorem foldl_one {Q : Type*} [Fintype Q] [DecidableEq Q] (B : ValAuto Q) (w : List (Fin 2)) :
    (w.foldl (stepF B) (1, 1)).2 = ((valW 1 w : ℕ) : ZMod 3) := by
  rw [foldl_stepF, W2a.valW_one]
  push_cast
  ring

theorem valW_snoc_append (r : ℕ) (w : List (Fin 2)) (b : Fin 2) (Y : List (Fin 2)) :
    valW r (w ++ [b] ++ Y) = (2 * valW r w + b) * 2 ^ Y.length + valW 0 Y := by
  rw [W3a.valW_append, valW_eq, W3a.valW_append]
  rfl

/-- Splitting a word into three parts at a window. -/
theorem split_window (W : Word) (i J : ℕ) : W = W.take i ++ window W i J ++ W.drop (i + J) := by
  unfold window
  rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]

theorem natCast_ne_zero_iff (x : ℕ) : ((x : ℕ) : ZMod 3) ≠ 0 ↔ ¬ 3 ∣ x := by
  rw [Ne, ZMod.natCast_eq_zero_iff]

/-! ## §1 The setting -/

/-- **The setting** (Definition 12.20 of the paper): for an automaton `B` all of whose components are 0/1, `u♯`, `R`, `β₀` and decomposition data. -/
structure Setup {Q : Type} [Fintype Q] [DecidableEq Q] (B : ValAuto Q) where
  h01 : ∀ C, IsComp B C → ZeroOne B C
  K : Set (BRel (ZIdx B))
  us : List (Fin 2)
  e : BRel (ZIdx B)
  hS : Sharp B K us e
  R : ℕ
  hR : Fintype.card Q ≤ R
  hR1 : 1 ≤ R
  β₀ : List Bool
  y'' : List (Fin 2)
  z : List (Fin 2)
  hy : (bitsMSB (parityOf β₀).length (terrasR (parityOf β₀))).map W3a.l2f = tailW us y'' z R
  D : DecompData B us [] y'' z R
  hD : ∀ γ, us.length ≤ D.t0 γ

namespace Setup

variable {Q : Type} [Fintype Q] [DecidableEq Q] {B : ValAuto Q} (S : Setup B)

/-- The top window `τ = (u♯)^R`. -/
def τ : List (Fin 2) := (List.replicate S.R S.us).flatten

/-- The length `E` of the top window. -/
def E : ℕ := S.τ.length

/-- `K = E + 9` of the point family. -/
def Kc : ℕ := S.E + 9

/-- The top part `T₀ = 1 τ 0^8` of `t` in the point family. -/
def T0 : ℕ := W3b.topT0 S.τ

/-- The length `s'` of the shared part. -/
def s' : ℕ := (parityOf S.β₀).length

/-- The state of the configuration automaton after reading `τ`. -/
noncomputable def P0 : PSt B := (S.e, ((valW 1 S.τ : ℕ) : ZMod 3))

/-- The state after reading `τ 0^8` (just before the free bits). -/
noncomputable def P1 : PSt B := (List.replicate 8 (0 : Fin 2)).foldl (stepF B) S.P0

/-- The residue of the point (reading the fixed word `z` after time `T`). -/
def endRes (c : PSt B) : ZMod 3 := 2 ^ S.z.length * c.2 + ((valW 0 S.z : ℕ) : ZMod 3)

/-- **The set of configurations** `𝔎`. -/
noncomputable def Kset : Finset (PSt B) :=
  Finset.univ.filter (fun c => Dfa.Reach (stepP B) S.P0 c ∧ c.1 * S.e = c.1 ∧ S.endRes c ≠ 0)

/-- The configuration of the point word `τ m y''(u♯)^R z`. -/
noncomputable def conf (m : List (Fin 2)) : PSt B := (m ++ S.y'' ++ S.τ).foldl (stepF B) S.P0

theorem us_ne_nil : S.us ≠ [] := S.hS.ne_nil

theorem us_length_pos : 0 < S.us.length := List.length_pos_iff.mpr S.us_ne_nil

theorem topW_eq : topW S.us [] S.R = S.τ := by simp [topW, τ]

theorem tailW_eq : tailW S.us S.y'' S.z S.R = S.y'' ++ S.τ ++ S.z := rfl

theorem fullW_eq (m : List (Fin 2)) :
    fullW S.us [] S.y'' S.z m S.R = S.τ ++ m ++ (S.y'' ++ S.τ ++ S.z) := by
  rw [fullW, S.topW_eq, S.tailW_eq]

theorem mu_tau : muZ B S.τ = S.e := S.hS.mu_pow B S.hR1

theorem tau_length : S.τ.length = S.R * S.us.length := by
  simp [τ, List.length_flatten, List.map_replicate, List.sum_replicate]

theorem foldl_tau : S.τ.foldl (stepF B) (1, 1) = S.P0 := by
  rw [foldl_stepF, one_mul, S.mu_tau, P0, W2a.valW_one]
  push_cast
  ring_nf

theorem posT_eq (m : List (Fin 2)) :
    posT S.us [] S.y'' m S.R = S.τ.length + m.length + S.y''.length + S.τ.length := by
  rw [posT, S.topW_eq, S.tau_length]

theorem take_posT (m : List (Fin 2)) :
    (fullW S.us [] S.y'' S.z m S.R).take (posT S.us [] S.y'' m S.R) = S.τ ++ m ++ S.y'' ++ S.τ := by
  rw [S.fullW_eq, S.posT_eq]
  have e : S.τ ++ m ++ (S.y'' ++ S.τ ++ S.z) = (S.τ ++ m ++ S.y'' ++ S.τ) ++ S.z := by
    simp only [List.append_assoc]
  rw [e, List.take_append_of_le_length (by simp only [List.length_append]; omega),
    List.take_of_length_le (by simp only [List.length_append]; omega)]

/-- The first component of the configuration is `s_T`. -/
theorem conf_fst (m : List (Fin 2)) : (S.conf m).1 = S.D.sT m := by
  rw [conf, foldl_stepF, DecompData.sT, S.take_posT]
  show S.e * muZ B (m ++ S.y'' ++ S.τ) = muZ B (S.τ ++ m ++ S.y'' ++ S.τ)
  rw [← S.mu_tau, ← muZ_append]
  simp only [List.append_assoc]

theorem conf_eq_foldl (m : List (Fin 2)) :
    S.conf m = (S.τ ++ m ++ S.y'' ++ S.τ).foldl (stepF B) (1, 1) := by
  rw [conf, show S.τ ++ m ++ S.y'' ++ S.τ = S.τ ++ (m ++ S.y'' ++ S.τ) by simp only [List.append_assoc]]
  conv_rhs => rw [List.foldl_append, S.foldl_tau]

/-- The residue of the point is `endRes (conf m)`. -/
theorem valW_res (m : List (Fin 2)) :
    ((valW 1 (fullW S.us [] S.y'' S.z m S.R) : ℕ) : ZMod 3) = S.endRes (S.conf m) := by
  rw [S.fullW_eq]
  have e : S.τ ++ m ++ (S.y'' ++ S.τ ++ S.z) = (S.τ ++ m ++ S.y'' ++ S.τ) ++ S.z := by
    simp only [List.append_assoc]
  rw [e, W3a.valW_append, valW_eq, endRes, S.conf_eq_foldl, foldl_one B]
  push_cast
  ring

theorem conf_mul_e (m : List (Fin 2)) : (S.conf m).1 * S.e = (S.conf m).1 := by
  rw [conf, foldl_stepF, muZ_append, S.mu_tau]
  simp only [mul_assoc, S.hS.idem]

theorem conf_reach (m : List (Fin 2)) : Dfa.Reach (stepP B) S.P0 (S.conf m) :=
  ⟨(m ++ S.y'' ++ S.τ).map W3d.f2b, by rw [run_stepP]; rfl⟩

/-- The configuration of a point with `3 ∤ x` lies in `𝔎`. -/
theorem conf_mem (m : List (Fin 2)) (h : ¬ 3 ∣ valW 1 (fullW S.us [] S.y'' S.z m S.R)) :
    S.conf m ∈ S.Kset := by
  unfold Kset
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, S.conf_reach m, S.conf_mul_e m, ?_⟩
  rw [← S.valW_res]
  exact (natCast_ne_zero_iff _).2 h

/-- The point of a configuration of `𝔎` is not a multiple of 3. -/
theorem not_dvd_of_conf (m : List (Fin 2)) (h : S.conf m ∈ S.Kset) :
    ¬ 3 ∣ valW 1 (fullW S.us [] S.y'' S.z m S.R) := by
  unfold Kset at h
  rw [Finset.mem_filter] at h
  rw [← natCast_ne_zero_iff, S.valW_res]
  exact h.2.2.2

/-- `𝔎` is non-empty (changing one letter of the middle word changes the residue of the point). -/
theorem Kset_nonempty : S.Kset.Nonempty := by
  have h0 := S.valW_res [0]
  have h1 := S.valW_res [1]
  rw [S.fullW_eq] at h0 h1
  set Y := S.y'' ++ S.τ ++ S.z
  have hval : ∀ b : Fin 2, valW 1 (S.τ ++ [b] ++ Y) = (2 * valW 1 S.τ + b) * 2 ^ Y.length + valW 0 Y :=
    fun b => valW_snoc_append 1 S.τ b Y
  have key : ((valW 1 (S.τ ++ [1] ++ Y) : ℕ) : ZMod 3) =
      ((valW 1 (S.τ ++ [0] ++ Y) : ℕ) : ZMod 3) + 2 ^ Y.length := by
    rw [hval, hval]
    simp only [Fin.val_one, Fin.val_zero]
    push_cast
    ring
  by_cases hz : ((valW 1 (S.τ ++ [0] ++ Y) : ℕ) : ZMod 3) = 0
  · refine ⟨S.conf [1], S.conf_mem [1] ?_⟩
    rw [← natCast_ne_zero_iff, S.fullW_eq, key, hz, zero_add]
    rcases two_pow_zmod3 Y.length with h | h <;> rw [h] <;> decide
  · refine ⟨S.conf [0], S.conf_mem [0] ?_⟩
    rw [← natCast_ne_zero_iff, S.fullW_eq]
    exact hz

/-! ## §2 Recurrence and the event (c) -/

theorem P0_recurrent : Dfa.Recurrent (stepP B) S.P0 :=
  recurrent_of_mem B S.hS.minIdeal S.hS.mem _

theorem P1_reach : Dfa.Reach (stepP B) S.P0 S.P1 :=
  ⟨(List.replicate 8 (0 : Fin 2)).map W3d.f2b, by rw [run_stepP]; rfl⟩

theorem P1_recurrent : Dfa.Recurrent (stepP B) S.P1 := S.P0_recurrent.of_reach S.P1_reach

/-- A length matching a class of `ZMod`: some `F` with `F₀ ≤ F < F₀ + p` has `(F : ZMod p) = i`. -/
theorem exists_len_cls {p : ℕ} (hp : 0 < p) (i : ZMod p) (F₀ : ℕ) :
    ∃ F, F₀ ≤ F ∧ F < F₀ + p ∧ ((F : ℕ) : ZMod p) = i := by
  have : NeZero p := ⟨by omega⟩
  refine ⟨F₀ + (i - (F₀ : ZMod p)).val, Nat.le_add_right _ _,
    by have := ZMod.val_lt (i - (F₀ : ZMod p)); omega, ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val]
  ring

/-- **The event (c)** (Lemma 12.21 (v) of the paper): there is `L` such that for every configuration `c` of `𝔎` and every word `w` there is a target state `b` (reachable from `P₁`)
from which reading `w (u♯)^R` gives `c`, and if the length `F ≥ L` matches the class `cls b`, then at least `2^{F-L}` free-bit words of `F` digits
lead from `P₁` to `b`. -/
theorem eventC : ∃ L : ℕ, ∀ c ∈ S.Kset, ∀ w : List (Fin 2), ∃ b : PSt B,
    (w ++ S.τ).foldl (stepF B) b = c ∧
    ∀ F, L ≤ F → ((F : ℕ) : ZMod (Dfa.period (stepP B) S.P1)) = Dfa.cls (stepP B) S.P1 b →
      2 ^ (F - L) ≤ ((Finset.range (2 ^ F)).filter (fun u =>
        ((bitsMSB F u).map W3a.l2f).foldl (stepF B) S.P1 = b)).card := by
  obtain ⟨L, hL⟩ := Dfa.count_words S.P1_recurrent
  refine ⟨L, fun c hc w => ?_⟩
  unfold Kset at hc
  rw [Finset.mem_filter] at hc
  obtain ⟨-, hreach, hce, -⟩ := hc
  obtain ⟨v, hv⟩ := realize B S.hS S.hR1 hce c.2 w
  refine ⟨v.foldl (stepF B) (c.1, c.2), hv, fun F hF hcls => ?_⟩
  -- `b` is reachable from `P₁`
  have hc1 : Dfa.Reach (stepP B) S.P1 c := by
    have hback := S.P0_recurrent S.P1 S.P1_reach
    exact hback.trans hreach
  have hb1 : Dfa.Reach (stepP B) S.P1 (v.foldl (stepF B) (c.1, c.2)) :=
    hc1.trans ⟨v.map W3d.f2b, by rw [run_stepP]⟩
  have hcnt := hL F hF S.P1 _ (Dfa.Reach.refl S.P1) hb1 (by rw [Dfa.cls_self S.P1_recurrent, zero_add, hcls])
  have h2 := card_range_bits F (fun g => Dfa.run (stepP B) S.P1 g = v.foldl (stepF B) (c.1, c.2))
  have hfil : (Finset.range (2 ^ F)).filter (fun u =>
        ((bitsMSB F u).map W3a.l2f).foldl (stepF B) S.P1 = v.foldl (stepF B) (c.1, c.2)) =
      (Finset.range (2 ^ F)).filter (fun u =>
        Dfa.run (stepP B) S.P1 ((bitsMSB F u).map W3d.toB) = v.foldl (stepF B) (c.1, c.2)) := by
    apply Finset.filter_congr
    intro u _
    have e : (bitsMSB F u).map W3d.toB = ((bitsMSB F u).map W3a.l2f).map W3d.f2b := by
      rw [List.map_map]
      refine List.map_congr_left (fun s _ => ?_)
      simp only [Function.comp_apply, W3a.l2f, W3d.f2b, W3d.toB]
      by_cases h : s = Letter.t <;> simp [h]
    rw [e, run_stepP]
  rw [hfil]
  refine le_trans hcnt (le_of_eq ?_)
  convert h2.symm

/-! ## §3 The word of the starting point -/

/-- The length of the free bits, `F = n - K - s'`. -/
def Flen (n : ℕ) : ℕ := n - S.Kc - S.s'

/-- The middle of the word of the starting point: `0^8 · u · ρ · r'`. -/
def mid0 (β : List Bool) (n u : ℕ) : List (Fin 2) :=
  List.replicate 8 0 ++ (bitsMSB (S.Flen n) u).map W3a.l2f ++
    (bitsMSB S.s' (famRho S.β₀ β)).map W3a.l2f ++
    (bitsMSB ((parityOf β).length - S.s') (famRtop S.β₀ β)).map W3a.l2f

theorem T0_bounds : 2 ^ (S.Kc - 1) ≤ S.T0 ∧ S.T0 < 2 ^ S.Kc := by
  have := W3b.topT0_bounds S.τ
  refine ⟨?_, ?_⟩
  · rw [show S.Kc - 1 = S.τ.length + 8 by simp [Kc, E]]; exact this.1
  · rw [show S.Kc = S.τ.length + 9 by simp [Kc, E]]; exact this.2

theorem T0_pos : 1 ≤ S.T0 := le_trans Nat.one_le_two_pow S.T0_bounds.1

/-- **The word of the starting point**: `binWord x₀ = τ · (0^8 · u · ρ · r') · y''(u♯)^R z` (`β = β₀ ++ β'`). -/
theorem binWord_x0 (β' : List Bool) {n u : ℕ} (hKn : S.Kc + S.s' ≤ n) (hu : u < 2 ^ S.Flen n) :
    binWord (famX0 S.β₀ (S.β₀ ++ β') n S.Kc S.T0 u) =
      fullW S.us [] S.y'' S.z (S.mid0 (S.β₀ ++ β') n u) S.R := by
  have hpre : S.β₀ <+: S.β₀ ++ β' := List.prefix_append _ _
  simp only [Flen, s'] at hKn hu ⊢
  rw [W3a.binWord_famX0 hKn S.T0_pos hu, ← W3a.binWord_eq_map, T0, W3b.binWord_topT0]
  have hsplit : bitsMSB (parityOf (S.β₀ ++ β')).length (terrasR (parityOf (S.β₀ ++ β'))) =
      bitsMSB ((parityOf (S.β₀ ++ β')).length - (parityOf S.β₀).length) (famRtop S.β₀ (S.β₀ ++ β')) ++
        bitsMSB (parityOf S.β₀).length (terrasR (parityOf S.β₀)) := by
    have hle := fam_s_le hpre
    have h1 := bitsMSB_add_mul ((parityOf (S.β₀ ++ β')).length - (parityOf S.β₀).length)
      (parityOf S.β₀).length
      (famRtop S.β₀ (S.β₀ ++ β')) (terrasR (parityOf S.β₀)) (fam_rtop_lt hpre) (terrasR_lt _)
    rw [Nat.sub_add_cancel hle, ← fam_terrasR_split hpre] at h1
    exact h1
  rw [hsplit, List.map_append, S.hy, S.fullW_eq, mid0, S.tailW_eq]
  simp only [List.append_assoc, Flen, s']

/-! ## §4 The choice of `β₀` -/

/-- If the window frequencies are close to uniform (`δ < 2^{-J}/2`), every digit word of length `J` occurs. -/
theorem occ_of_winClose {W : Word} {a b J : ℕ} {δ : ℚ} (h : WinClose W a b J δ) (hδ : 2 * δ < 1 / 2 ^ J)
    {v : Word} (hv : v ∈ wordsOfLen J) : ∃ i, window W i J = v := by
  obtain ⟨hab, -, hsum⟩ := h
  have hle := Finset.single_le_sum (f := fun v => |((winCount W a b J v : ℚ) / ((b + 1 - J - a : ℕ) : ℚ)) -
    1 / 2 ^ J|) (fun _ _ => abs_nonneg _) hv
  have hlt : |((winCount W a b J v : ℚ) / ((b + 1 - J - a : ℕ) : ℚ)) - 1 / 2 ^ J| < 1 / 2 ^ J :=
    lt_of_le_of_lt (le_trans hle hsum) hδ
  have hpos : 0 < winCount W a b J v := by
    by_contra h0
    push Not at h0
    have : winCount W a b J v = 0 := by omega
    rw [this] at hlt
    simp at hlt
  unfold winCount at hpos
  obtain ⟨i, hi⟩ := List.exists_mem_of_length_pos hpos
  exact ⟨i, by simpa using (List.mem_filter.mp hi).2⟩

/-- **The choice of `β₀`** (Lemma 12.21 (i) of the paper): for every word `w` there is `β₀` whose word of `r_{σ₀}` contains `w`. -/
theorem exists_beta0 (w : List (Fin 2)) : ∃ β₀ : List Bool, ∃ y'' z : List (Fin 2),
    (bitsMSB (parityOf β₀).length (terrasR (parityOf β₀))).map W3a.l2f = y'' ++ w ++ z := by
  set J := w.length
  obtain ⟨k₀, hk₀⟩ := hTerrasWin [] J (1 / 2 ^ (J + 2)) (1 / 2) (1 / 2) (by positivity) (by norm_num) (by norm_num)
  set k := max k₀ 1
  have hP := hk₀ k (le_max_left _ _) 0 k (by simp) (by
    have : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    push_cast; linarith) (by simp)
  have hpos : 0 < Prσ [] k (fun β => WinClose (bitsMSB (parityOf β).length (terrasR (parityOf β)))
      ((parityOf β).length - blockEnd β k) ((parityOf β).length - blockEnd β 0) J (1 / 2 ^ (J + 2))) := by
    linarith
  obtain ⟨β', hβ', hW⟩ := exists_of_Prσ_pos [] k _ hpos
  set β := [] ++ β'
  have hlen : β.length = k := by simp [β, length_of_mem_blockChoices hβ']
  have hend : blockEnd β k = (parityOf β).length := by
    unfold blockEnd; rw [List.take_of_length_le (by omega)]
  have h0 : blockEnd β 0 = 0 := by simp [blockEnd, parityOf]
  rw [hend, h0, Nat.sub_self, Nat.sub_zero] at hW
  have hv : w.map bitLetter ∈ wordsOfLen J := by
    refine mem_wordsOfLen_of (by simp [J]) ?_
    intro s hs
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hs
    unfold bitLetter; split_ifs <;> simp
  have hδ : 2 * (1 / 2 ^ (J + 2) : ℚ) < 1 / 2 ^ J := by
    rw [pow_add]; field_simp; norm_num
  obtain ⟨i, hi⟩ := occ_of_winClose hW hδ hv
  refine ⟨β, ((bitsMSB (parityOf β).length (terrasR (parityOf β))).take i).map W3a.l2f,
    ((bitsMSB (parityOf β).length (terrasR (parityOf β))).drop (i + J)).map W3a.l2f, ?_⟩
  have hl2f : (w.map bitLetter).map W3a.l2f = w := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id w]
    refine List.map_congr_left (fun b _ => ?_)
    fin_cases b <;> rfl
  conv_lhs => rw [split_window (bitsMSB (parityOf β).length (terrasR (parityOf β))) i J, hi]
  simp only [List.map_append, hl2f]

end Setup

end Collatz.Arctic.NatQ5.W3h
