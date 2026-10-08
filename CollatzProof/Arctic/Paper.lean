/-
The Lean results of this paper (the arctic barrier), restated under names that follow the numbering of the paper (the root module).
Names have the form `paper_<kind>_<section>_<number>[_<target>]` (Appendix A of the paper).

* Roles: (a) aliases following the numbering of the paper (`theorem paper_… : <existing statement> := <existing theorem>`; the type is a copy of the existing statement),
  (b) two new kinds of theorems, which combine theorems of other files, (c) the root module: every file of `Arctic/` lies in the import closure of this file
  (`leanchecker --fresh CollatzProof.Arctic.Paper` is run once).
* Files: Sections 2 and 3 here, Section 4 in `Paper2.lean`, Sections 5–8 and Appendix B in `Paper3.lean` (including Theorem 5.5), Proposition 9.5 in `Paper4.lean`, Sections 9–13, Appendix D and the remarks on argument filters (after Theorem 3.4) and on [YAH, Theorem 3.10] (Section 13.2) in `Paper5.lean`, which also imports the files of `Nat/` and `DPFilter*.lean`.
* New theorems:
  - `paper_thm_3_1_Hrev` (Theorem 3.1, rule removal for the reversed $\mathcal H$, unconditional): the transposition implication
    `HTPDB.NonVacuityH.barrier_HTrev_of` applied to `HTPDB.arcticBarrierHT`.
  - `paper_thm_3_6_T_Z`, `paper_thm_3_6_H_Z` (Theorem 3.6 as stated in the paper): there is no value `V = autoValZ u A c` of a max-plus automaton
    (entries in ℤ ∪ {−∞}, reading from the most significant digit, a natural number for `n ≥ 1`) with `V(f(x)) ≤ V(x) - 1` at every point of the domain;
    `paper_thm_3_6_T_Zlsb`, `paper_thm_3_6_H_Zlsb`: the same for values read from the least significant digit (reduced to `_Z` by transposition, `lsb_eq_autoValZ`).
    The domain is `2 ≤ x` for $T$ and `HModel.HDom x` for $H$. Proof of `_Z` (`noRankZ_of_autoCoreG`): Theorem 5.5 and the translation of Lemma 5.3 (`Gen.barrier_of_auto_arcZG`, slope `κ = K`),
    applied to a dynamic rule that is used at most once in the canonical derivation of each point (`f. → .` for $T$, `ff. → 0.` for $H$).
  - `paper_thm_3_6_T`, `paper_thm_3_6_H`: Theorem 3.6 for weights in `𝔸_ℕ` (entries in ℕ ∪ {−∞}, values finite for `n ≥ 1`; the formal status line of Theorem 3.6 lists them last), proved without the translation: the counting form of
    Theorem 5.5 with slope `κ = 0` for the same rule gives an orbit segment `n → f^[m] n` with `V(n) < (number of uses) ≤ m`, while `V(n) ≥ m` because the value decreases by at least 1 at each step and stays ≥ 0.
-/
import CollatzProof.Arctic.Paper2
import CollatzProof.Arctic.Paper3
import CollatzProof.Arctic.HTPDB.Final
import CollatzProof.Arctic.RH.Rev
import CollatzProof.Arctic.RH.Check
import CollatzProof.Arctic.Gen.TCheck
import CollatzProof.Arctic.DPGen.HCheck
import CollatzProof.Arctic.Affine.Fin
import CollatzProof.Arctic.Affine.Top
import CollatzProof.Arctic.Paper4
import CollatzProof.Arctic.Paper5

namespace Collatz.Arctic.Paper

open Collatz.Arctic Matrix

/-! ## Section 2: Preliminaries -/

/-- **Lemma 2.3** (canonical derivations of $\mathcal T$). -/
theorem paper_lem_2_3_T (n : ℕ) (hn : 2 ≤ n) : Chain (canDeriv n) (can n) (can (T n)) :=
  canDeriv_chain n hn

/-- **Lemma 2.3** (canonical derivations of $\mathcal H$). -/
theorem paper_lem_2_3_H (n : ℕ) (hn : HModel.HDom n) :
    Chain (HTPDB.canDerivH n) (can n) (can (HModel.Hmap n)) :=
  HTPDB.canDerivH_chain n hn

/-- **Lemma 2.3** (canonical derivations of $R_H$). -/
theorem paper_lem_2_3_RH (n : ℕ) (hn : HModel.HDom n) :
    Chain (RH.canDerivRH n) (RH.canRH n) (RH.canRH (HModel.Hmap n)) :=
  RH.canDerivRH_chain n hn

/-! ## Section 3: Main results -/

/-- **Theorem 3.1** ($\mathcal T$, rule removal). -/
theorem paper_thm_3_1_T : ArcticBarrierST := arcticBarrierST
/-- **Theorem 3.1** ($\mathcal H$). -/
theorem paper_thm_3_1_H : HTPDB.ArcticBarrierHT := HTPDB.arcticBarrierHT
/-- **Theorem 3.1** ($R_H$, the 10 used rules). -/
theorem paper_thm_3_1_RH : RH.ArcticBarrierRH := RH.arcticBarrierRH
/-- **Theorem 3.1** (subsystems of $R_H$). -/
theorem paper_thm_3_1_RHsub : RH.ArcticBarrierRHSub := RH.arcticBarrierRHSub
/-- **Theorem 3.1** (the reversed $\mathcal T$). -/
theorem paper_thm_3_1_Trev : NonVacuity.BarrierFor NonVacuity.rulesSTrev := NonVacuity.barrier_STrev
/-- **Theorem 3.1** (the reversed $\mathcal H$; a new combination: the transposition implication applied to the unconditional theorem). -/
theorem paper_thm_3_1_Hrev : NonVacuity.BarrierFor HTPDB.NonVacuityH.rulesHTrev :=
  HTPDB.NonVacuityH.barrier_HTrev_of HTPDB.arcticBarrierHT
/-- **Theorem 3.1** (the reversed $R_H$: the reversals of the 10 used rules). -/
theorem paper_thm_3_1_RHrev : NonVacuity.BarrierFor (RH.usedRH.map NonVacuity.revRule) :=
  RH.arcticBarrierRHrev

/-- **Theorem 3.3** (dependency pairs, `𝔸_ℕ`). -/
theorem paper_thm_3_3_T : ArcticBarrierDP := arcticBarrierDP
theorem paper_thm_3_3_Trev : ArcticBarrierDPrev := arcticBarrierDPrev
theorem paper_thm_3_3_H : HTPDB.ArcticBarrierHDP := HTPDB.arcticBarrierHDP
theorem paper_thm_3_3_Hrev : HTPDB.ArcticBarrierHDPrev := HTPDB.arcticBarrierHDPrev

/-- **Theorem 3.4** (dependency pairs, below zero). -/
theorem paper_thm_3_4_T : ArcticBarrierBZ := arcticBarrierBZ
theorem paper_thm_3_4_Trev : ArcticBarrierBZrev := arcticBarrierBZrev
theorem paper_thm_3_4_H : HTPDB.ArcticBarrierHBZ := HTPDB.arcticBarrierHBZ
theorem paper_thm_3_4_Hrev : HTPDB.ArcticBarrierHBZrev := HTPDB.arcticBarrierHBZrev

/-! ### Ingredients of the proof of Theorem 3.6 -/

/-- From the counting form for one rule `ρ` (`Gen.AutoRuleG`, used with slope `κ = 0`), the fact that `ρ` is used at most once in the canonical derivation
of each point, and the fact that images of points of the domain are at least 1: the negation of the ranking function form (entries in ℕ ∪ {−∞}). -/
theorem noRank_of_autoRuleG {f : ℕ → ℕ} {dom : ℕ → Prop} {cd : ℕ → List Rule} {ρ : Rule}
    (hcore : Gen.AutoRuleG f dom cd ρ) (hcnt : ∀ n, (cd n).count ρ ≤ 1)
    (hpos : ∀ n, dom n → 1 ≤ f n) :
    ¬ ∃ (D : ℕ) (u : Fin D → Arc) (A : Interp D) (c : Fin D → Arc),
      (∀ n, 1 ≤ n → autoVal u A c n ≠ 0) ∧
      ∀ n, dom n → ∀ a b : ℕ, autoVal u A c n = Arc.fin a → autoVal u A c (f n) = Arc.fin b →
        b + 1 ≤ a := by
  rintro ⟨D, u, A, c, hfin, hdec⟩
  have hex : ∀ n, 1 ≤ n → ∃ a : ℕ, autoVal u A c n = Arc.fin a := fun n hn =>
    (Arc.val_ne_bot_iff _).mp fun h => hfin n hn (Arc.ext (by rw [h]; rfl))
  obtain ⟨n, hn, m, hm, hlt⟩ := hcore D u A c 0 hfin
    (fun n hn a b ha hb => by have := hdec n hn a b ha hb; omega) 1
  obtain ⟨a₀, ha₀⟩ := hex n hn
  -- Along the orbit segment the value decreases by at least 1 at each step and stays finite
  have key : ∀ i, i ≤ m → ∃ a : ℕ, autoVal u A c (f^[i] n) = Arc.fin a ∧ a + i ≤ a₀ := by
    intro i
    induction i with
    | zero => intro _; exact ⟨a₀, ha₀, le_refl _⟩
    | succ i ih =>
      intro hi
      obtain ⟨a, ha, hai⟩ := ih (by omega)
      have hd : dom (f^[i] n) := hm i (by omega)
      have hs : f^[i + 1] n = f (f^[i] n) := Function.iterate_succ_apply' f i n
      obtain ⟨b, hb⟩ := hex (f^[i + 1] n) (hs ▸ hpos _ hd)
      exact ⟨b, hb, by have := hdec _ hd a b ha (hs ▸ hb); omega⟩
  obtain ⟨_, -, hm₀⟩ := key m le_rfl
  -- The number of uses is at most the number of steps
  have huses : ∀ k, Gen.usesOrbitG f cd ρ n k ≤ k := by
    intro k
    induction k with
    | zero => simp [Gen.usesOrbitG]
    | succ k ih =>
      unfold Gen.usesOrbitG at ih ⊢
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have := hcnt (f^[k] n)
      omega
  have := huses m
  rw [ha₀, Arc.fin_lt_fin] at hlt
  omega

/-- The form with entries in ℤ ∪ {−∞}: from `AutoCoreG` and a rule `ρ` used at most once at each point (translation, `Gen.barrier_of_auto_arcZG`). -/
theorem noRankZ_of_autoCoreG {f : ℕ → ℕ} {dom : ℕ → Prop} {rules : List Rule}
    {cd : ℕ → List Rule} (hcore : Gen.AutoCoreG f dom rules cd) {ρ : Rule} (hρ : ρ ∈ rules)
    (hcnt : ∀ n, (cd n).count ρ ≤ 1) :
    ¬ ∃ (D : ℕ) (u : Fin D → ArcZ) (A : Letter → Matrix (Fin D) (Fin D) ArcZ) (c : Fin D → ArcZ),
      (∀ n, 1 ≤ n → ∃ z : ℕ, autoValZ u A c n = ArcZ.fin z) ∧
      ∀ n, dom n → ∀ a b : ℤ, autoValZ u A c n = ArcZ.fin a →
        autoValZ u A c (f n) = ArcZ.fin b → b + 1 ≤ a := by
  rintro ⟨D, u, A, c, hnn, hdec⟩
  have hnn' : ∀ n, ∃ z : ℕ, autoValZ u A c n = ArcZ.fin z := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hb : binTail 0 = binTail 1 := by simp [binTail]
      have h01 : autoValZ u A c 0 = autoValZ u A c 1 := by simp only [autoValZ, hb]
      rw [h01]; exact hnn 1 le_rfl
    · exact hnn n hn
  refine Gen.barrier_of_auto_arcZG hcore u A c ρ hρ hnn' fun n hn => ?_
  obtain ⟨a, ha⟩ := hnn' n
  obtain ⟨b, hb⟩ := hnn' (f n)
  have h1 := hdec n hn a b ha hb
  have h2 := hcnt n
  rw [ha, hb, ArcZ.fin_pow, ArcZ.fin_mul_fin, ArcZ.fin_le_fin]
  omega

/-- The matrix product of the reversed word is the transpose of the product of the transposed matrices. -/
theorem evR_reverse {D : ℕ} (A : Letter → Matrix (Fin D) (Fin D) ArcZ) (w : Word) :
    evR A w.reverse = (evR (fun s => (A s)ᵀ) w)ᵀ := by
  induction w with
  | nil => simp [evR]
  | cons s w ih =>
    rw [List.reverse_cons, evR_append, ih]
    simp [evR, Matrix.transpose_mul]

/-- The value read from the least significant digit is the value of the transposed automaton read from the most significant digit. -/
theorem lsb_eq_autoValZ {D : ℕ} (u : Fin D → ArcZ) (A : Letter → Matrix (Fin D) (Fin D) ArcZ)
    (c : Fin D → ArcZ) (n : ℕ) :
    u ⬝ᵥ (evR A (binTail n).reverse *ᵥ c) = autoValZ c (fun s => (A s)ᵀ) u n := by
  rw [evR_reverse, mulVec_transpose, autoValZ, dotProduct_mulVec, dotProduct_comm]

/-- `f. → .` is used at most once in the canonical derivation of each point for $\mathcal T$. -/
theorem count_fRule_le_one (n : ℕ) :
    (canDeriv n).count ⟨[Letter.f, Letter.rgt], [Letter.rgt]⟩ ≤ 1 := by
  show uses _ n ≤ 1
  rw [fam_uses_even]
  split_ifs <;> omega

/-- `ff. → 0.` is used at most once in the canonical derivation of each point for $\mathcal H$. -/
theorem count_ffRule_le_one (n : ℕ) : (HTPDB.canDerivH n).count HTPDB.ffRule ≤ 1 := by
  by_cases h4 : n % 4 = 0
  · exact (HTPDB.UsesH.count_of_A h4).1.le
  · by_cases h8 : n % 8 = 7
    · rw [(HTPDB.UsesH.count_of_B h8).1]; omega
    · simp [HTPDB.canDerivH, h4, h8]

/-! ### Theorem 3.6 -/

/-- **Theorem 3.6 ($T$) for weights in `𝔸_ℕ`** (a special case of `paper_thm_3_6_T_Z`, proved without the translation): there is no value `V = autoVal u A c`
of a max-plus automaton with entries in ℕ ∪ {−∞} (finite for `n ≥ 1`) such that `V(T n) ≤ V(n) - 1` for all `n` with `2 ≤ n`. -/
theorem paper_thm_3_6_T : ¬ ∃ (D : ℕ) (u : Fin D → Arc) (A : Interp D) (c : Fin D → Arc),
    (∀ n, 1 ≤ n → autoVal u A c n ≠ 0) ∧
    ∀ n, 2 ≤ n → ∀ a b : ℕ, autoVal u A c n = Arc.fin a → autoVal u A c (T n) = Arc.fin b →
      b + 1 ≤ a :=
  noRank_of_autoRuleG (f := T) (dom := fun n => 2 ≤ n) (cd := canDeriv)
    (fun D u A c κ hfin hsl N => paper_thm_5_5_T D u A c κ hfin hsl _ (by decide) N)
    count_fRule_le_one (fun n hn => by unfold T; split_ifs <;> omega)

/-- **Theorem 3.6 ($H$) for weights in `𝔸_ℕ`** (a special case of `paper_thm_3_6_H_Z`, proved without the translation): there is no value `V = autoVal u A c`
of a max-plus automaton with entries in ℕ ∪ {−∞} (finite for `n ≥ 1`) such that `V(H n) ≤ V(n) - 1` for all `n` with `HModel.HDom n`. -/
theorem paper_thm_3_6_H : ¬ ∃ (D : ℕ) (u : Fin D → Arc) (A : Interp D) (c : Fin D → Arc),
    (∀ n, 1 ≤ n → autoVal u A c n ≠ 0) ∧
    ∀ n, HModel.HDom n → ∀ a b : ℕ, autoVal u A c n = Arc.fin a →
      autoVal u A c (HModel.Hmap n) = Arc.fin b → b + 1 ≤ a :=
  noRank_of_autoRuleG (f := HModel.Hmap) (dom := HModel.HDom) (cd := HTPDB.canDerivH)
    (fun D u A c κ hfin hsl N => paper_thm_5_5_H D u A c κ hfin hsl HTPDB.ffRule (by decide) N)
    count_ffRule_le_one
    (fun n hn => by unfold HModel.HDom at hn; unfold HModel.Hmap; split_ifs <;> omega)

/-- **Theorem 3.6 ($T$)** as stated in the paper: entries in ℤ ∪ {−∞}, values natural numbers for `n ≥ 1`, digits read from the most significant end. -/
theorem paper_thm_3_6_T_Z : ¬ ∃ (D : ℕ) (u : Fin D → ArcZ)
    (A : Letter → Matrix (Fin D) (Fin D) ArcZ) (c : Fin D → ArcZ),
    (∀ n, 1 ≤ n → ∃ z : ℕ, autoValZ u A c n = ArcZ.fin z) ∧
    ∀ n, 2 ≤ n → ∀ a b : ℤ, autoValZ u A c n = ArcZ.fin a →
      autoValZ u A c (T n) = ArcZ.fin b → b + 1 ≤ a :=
  noRankZ_of_autoCoreG (dom := fun n => 2 ≤ n) paper_thm_5_5_T (by decide) count_fRule_le_one

/-- **Theorem 3.6 ($H$)** as stated in the paper: entries in ℤ ∪ {−∞}, values natural numbers for `n ≥ 1`, digits read from the most significant end. -/
theorem paper_thm_3_6_H_Z : ¬ ∃ (D : ℕ) (u : Fin D → ArcZ)
    (A : Letter → Matrix (Fin D) (Fin D) ArcZ) (c : Fin D → ArcZ),
    (∀ n, 1 ≤ n → ∃ z : ℕ, autoValZ u A c n = ArcZ.fin z) ∧
    ∀ n, HModel.HDom n → ∀ a b : ℤ, autoValZ u A c n = ArcZ.fin a →
      autoValZ u A c (HModel.Hmap n) = ArcZ.fin b → b + 1 ≤ a :=
  noRankZ_of_autoCoreG paper_thm_5_5_H (by decide) count_ffRule_le_one

/-- **Theorem 3.6 ($T$)**, last sentence: the same for values that read the digits from the least significant end. -/
theorem paper_thm_3_6_T_Zlsb : ¬ ∃ (D : ℕ) (u : Fin D → ArcZ)
    (A : Letter → Matrix (Fin D) (Fin D) ArcZ) (c : Fin D → ArcZ),
    (∀ n, 1 ≤ n → ∃ z : ℕ, u ⬝ᵥ (evR A (binTail n).reverse *ᵥ c) = ArcZ.fin z) ∧
    ∀ n, 2 ≤ n → ∀ a b : ℤ, u ⬝ᵥ (evR A (binTail n).reverse *ᵥ c) = ArcZ.fin a →
      u ⬝ᵥ (evR A (binTail (T n)).reverse *ᵥ c) = ArcZ.fin b → b + 1 ≤ a := by
  rintro ⟨D, u, A, c, hnn, hdec⟩
  simp only [lsb_eq_autoValZ] at hnn hdec
  exact paper_thm_3_6_T_Z ⟨D, c, _, u, hnn, hdec⟩

/-- **Theorem 3.6 ($H$)**, last sentence: the same for values that read the digits from the least significant end. -/
theorem paper_thm_3_6_H_Zlsb : ¬ ∃ (D : ℕ) (u : Fin D → ArcZ)
    (A : Letter → Matrix (Fin D) (Fin D) ArcZ) (c : Fin D → ArcZ),
    (∀ n, 1 ≤ n → ∃ z : ℕ, u ⬝ᵥ (evR A (binTail n).reverse *ᵥ c) = ArcZ.fin z) ∧
    ∀ n, HModel.HDom n → ∀ a b : ℤ, u ⬝ᵥ (evR A (binTail n).reverse *ᵥ c) = ArcZ.fin a →
      u ⬝ᵥ (evR A (binTail (HModel.Hmap n)).reverse *ᵥ c) = ArcZ.fin b → b + 1 ≤ a := by
  rintro ⟨D, u, A, c, hnn, hdec⟩
  simp only [lsb_eq_autoValZ] at hnn hdec
  exact paper_thm_3_6_H_Z ⟨D, c, _, u, hnn, hdec⟩

/-- **Proposition 3.7 ($T$)** (the carry rules are used quadratically). -/
theorem paper_prop_3_7_T (D : ℕ) (u : Fin D → Arc) (A : Interp D) (c : Fin D → Arc) (K : ℕ)
    (b d : ℕ) (hb : b < 2) (hd : d ≤ 2) (N : ℕ) :
    ∃ n, N ≤ n ∧ ∃ m : ℕ, (∀ i < m, 2 ≤ T^[i] n) ∧
      autoVal u A c n < Arc.fin (K * lenT n + usesOrbit (aRule b d) n m) :=
  autoCore_aRule D u A c K b d hb hd N

/-- **Proposition 3.7 ($H$)**. -/
theorem paper_prop_3_7_H : HTPDB.SpecQuadH := HTPDB.specQuadH

/-! ### Interpretations by arctic linear functions with absolute parts (Corollary 3.8, Proposition 4.8) -/

/-- **Corollary 3.8 ($\mathcal T$)**: absolute parts do not change the barrier if every $(M_\sigma)_{00}$ is finite. -/
theorem paper_cor_3_8_T : Affine.AffBarrierFin rulesST := Affine.affFin_ST
/-- **Corollary 3.8 (the reversed $\mathcal T$)**. -/
theorem paper_cor_3_8_Trev : Affine.AffBarrierFin NonVacuity.rulesSTrev := Affine.affFin_STrev
/-- **Corollary 3.8 ($\mathcal H$)**. -/
theorem paper_cor_3_8_H : Affine.AffBarrierFin HTPDB.rulesHT := Affine.affFin_HT
/-- **Corollary 3.8 (the reversed $\mathcal H$)**. -/
theorem paper_cor_3_8_Hrev : Affine.AffBarrierFin HTPDB.NonVacuityH.rulesHTrev := Affine.affFin_HTrev
/-- **Corollary 3.8 ($R_H$, the 10 used rules)**. -/
theorem paper_cor_3_8_RH : Affine.AffBarrierFin RH.usedRH := Affine.affFin_RH

/-- **Proposition 4.8 ($\mathcal T$)**: a somewhere finite interpretation by arctic linear functions (the class for top termination) can strictly orient the rule `ρ` and weakly
orient the others if and only if `ρ` is not a left-end rule. -/
theorem paper_prop_4_8_T (ρ : Rule) (hρ : ρ ∈ rulesST) :
    Affine.SomeFinOrientable rulesST ρ ↔ ρ ∉ Affine.leftST := Affine.someFinClass_iff_left_ST ρ hρ
/-- **Proposition 4.8 ($\mathcal H$)**. -/
theorem paper_prop_4_8_H (ρ : Rule) (hρ : ρ ∈ HTPDB.rulesHT) :
    Affine.SomeFinOrientable HTPDB.rulesHT ρ ↔ ρ ∉ Affine.leftST := Affine.someFinClass_iff_left_HT ρ hρ

end Collatz.Arctic.Paper
