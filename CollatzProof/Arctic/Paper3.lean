/-
Names following the numbering of the paper (the arctic barrier), part 3: Sections 5–8 and Appendix B. Imported by `Paper.lean`.
Names of the form described in Appendix A of the paper; the formal status lines of the paper cite them. All are aliases of existing theorems, and their types are copies of the statements of the existing theorems
(Lean checks that they agree with the type of the right-hand side of `:=`).

* Section 5: Lemma 5.1 (`phi_step_weak`, `phi_step_strict`), Theorem 5.5 (`AutoCore`, `HTPDB.AutoCoreH`),
  Lemma 5.6 (`DPGen.simulation_arc`, `simulation_arcZ`, family form `simulation_family_arc(Z)`).
  **Theorem 5.5 ($T$) is `autoCore_of_hyps hsp_holds hTerrasWin hLeftUse`** (it closes with theorems in the closure of `Summary` only;
  `DPGen.autoCore_holds` is the same term, but it lies in a file outside the closure of `Summary`).
* Section 6: Lemmas 6.2, 6.3, 6.5, 6.6, Proposition 6.7 (left-end rules), Theorem 6.8 (assembly).
* Section 7: Lemma 7.4 (`RH.canDerivRH_eq`), Proposition 7.5 (`RH.autoCoreRH_of_autoCoreH`).
* Section 8: Corollary 8.1 (`DPGen.autoRuleG_family`).
* Appendix B: Theorem B.1, Proposition B.2, Theorem B.3, Corollary B.4, Theorem B.7, Theorem B.8, Proposition B.9.
* Further aliases, cited in the formal status lines of the paper next to those above: `paper_lem_5_6_family`, `_familyZ`, `paper_lem_6_2_exists`,
  `paper_lem_7_4_count`, `paper_thm_B_1_at`, `paper_thm_B_3_spr`, `paper_thm_B_8_of_key`.
-/
import CollatzProof.Arctic.Summary
import CollatzProof.Arctic.RH.Final
import CollatzProof.Arctic.DPGen.HCheck

namespace Collatz.Arctic.Paper

open Collatz.Arctic

/-! ## Section 5: From rewriting to values -/

/-- **Lemma 5.1** (under weak orientation, `Φ` in a context does not increase). -/
theorem paper_lem_5_1_weak {d : ℕ} (hd : 0 < d) (I : Interp d) {ρ : Rule} (h : Weak I ρ)
    (p q : Word) : Phi hd I (p ++ ρ.rhs ++ q) ≤ Phi hd I (p ++ ρ.lhs ++ q) :=
  phi_step_weak hd I h p q

/-- **Lemma 5.1** (under strict orientation, `Φ` in a context decreases by at least 1). -/
theorem paper_lem_5_1_strict {d : ℕ} (hd : 0 < d) (I : Interp d) {ρ : Rule} (h : Strict I ρ)
    (p q : Word) {a : ℕ} (ha : Phi hd I (p ++ ρ.rhs ++ q) = Arc.fin a) :
    Arc.fin (a + 1) ≤ Phi hd I (p ++ ρ.lhs ++ q) :=
  phi_step_strict hd I h p q ha

/-- **Theorem 5.5 ($T$)**: `AutoCore` holds. -/
theorem paper_thm_5_5_T : AutoCore := autoCore_of_hyps hsp_holds hTerrasWin hLeftUse

/-- **Theorem 5.5 ($H$)**: `AutoCoreH` holds. -/
theorem paper_thm_5_5_H : HTPDB.AutoCoreH := RH.autoCoreH_holds

section Sim

open DPGen Gen

variable {α : Type} [DecidableEq α]

/-- **Lemma 5.6** (the simulation lemma, `𝔸_ℕ`). -/
theorem paper_lem_5_6 {f : ℕ → ℕ} {dom : ℕ → Prop} {cnt : ℕ → ℕ}
    (E : ℕ → List (GLetter α)) (U P : List (GDRule α)) (π : GDRule α)
    (ha : ∀ n, dom n → ∃ es, GDChain U P es (E n) (E (f n)) ∧ cnt n ≤ es.count (GLabel.root π))
    (hc : AutoUseG f dom cnt) {d : ℕ} (hd : 0 < d) (J : GLetter α → AffFun Arc d)
    (hb : ∃ (D : ℕ) (u : Fin D → Arc) (A : Interp D) (c : Fin D → Arc),
      ∀ n, gV hd J (E n) = autoVal u A c n)
    (hfin : ∀ n, gV hd J (E n) ≠ 0) (hU : ∀ ρ ∈ U, WeakA (gevA J ρ.lhs) (gevA J ρ.rhs))
    (hP : ∀ π' ∈ P, WeakTop hd (gevA J π'.lhs) (gevA J π'.rhs)) :
    ¬ StrictTop hd (gevA J π.lhs) (gevA J π.rhs) :=
  simulation_arc E U P π ha hc hd J hb hfin hU hP

/-- **Lemma 5.6** (the simulation lemma, below zero, `𝔸_ℤ`). -/
theorem paper_lem_5_6_Z {f : ℕ → ℕ} {dom : ℕ → Prop} {cnt : ℕ → ℕ}
    (E : ℕ → List (GLetter α)) (U P : List (GDRule α)) (π : GDRule α)
    (ha : ∀ n, dom n → ∃ es, GDChain U P es (E n) (E (f n)) ∧ cnt n ≤ es.count (GLabel.root π))
    (hc : AutoUseG f dom cnt) {d : ℕ} (hd : 0 < d) (J : GLetter α → AffFun ArcZ d)
    (hb : ∃ (D : ℕ) (u : Fin D → ArcZ) (A : Letter → Matrix (Fin D) (Fin D) ArcZ)
      (c : Fin D → ArcZ), ∀ n, gV hd J (E n) = autoValZ u A c n)
    (hlow : ∃ B : ℤ, ∀ n, ArcZ.fin B ≤ gV hd J (E n))
    (hU : ∀ ρ ∈ U, WeakA (gevA J ρ.lhs) (gevA J ρ.rhs))
    (hP : ∀ π' ∈ P, WeakTop hd (gevA J π'.lhs) (gevA J π'.rhs)) :
    ¬ StrictTop hd (gevA J π.lhs) (gevA J π.rhs) :=
  simulation_arcZ E U P π ha hc hd J hb hlow hU hP

/-- The family form of Lemma 5.6 (`𝔸_ℕ`; cited in the formal status line of Lemma 5.6). -/
theorem paper_lem_5_6_family (M : BlockModel) (hTW : HTerrasWinR M.R) {cnt : ℕ → ℕ}
    (hUse : HUseC M.f M.R M.steps cnt) (E : ℕ → List (GLetter α)) (U P : List (GDRule α))
    (π : GDRule α) (ha : ∀ n, famDom M n →
      ∃ es, GDChain U P es (E n) (E (M.f n)) ∧ cnt n ≤ es.count (GLabel.root π))
    {d : ℕ} (hd : 0 < d) (J : GLetter α → AffFun Arc d)
    (hb : ∃ (D : ℕ) (u : Fin D → Arc) (A : Interp D) (c : Fin D → Arc),
      ∀ n, gV hd J (E n) = autoVal u A c n)
    (hfin : ∀ n, gV hd J (E n) ≠ 0) (hU : ∀ ρ ∈ U, WeakA (gevA J ρ.lhs) (gevA J ρ.rhs))
    (hP : ∀ π' ∈ P, WeakTop hd (gevA J π'.lhs) (gevA J π'.rhs)) :
    ¬ StrictTop hd (gevA J π.lhs) (gevA J π.rhs) :=
  simulation_family_arc M hTW hUse E U P π ha hd J hb hfin hU hP

/-- The family form of Lemma 5.6 (below zero; cited in the formal status line of Lemma 5.6). -/
theorem paper_lem_5_6_familyZ (M : BlockModel) (hTW : HTerrasWinR M.R) {cnt : ℕ → ℕ}
    (hUse : HUseC M.f M.R M.steps cnt) (E : ℕ → List (GLetter α)) (U P : List (GDRule α))
    (π : GDRule α) (ha : ∀ n, famDom M n →
      ∃ es, GDChain U P es (E n) (E (M.f n)) ∧ cnt n ≤ es.count (GLabel.root π))
    {d : ℕ} (hd : 0 < d) (J : GLetter α → AffFun ArcZ d)
    (hb : ∃ (D : ℕ) (u : Fin D → ArcZ) (A : Letter → Matrix (Fin D) (Fin D) ArcZ)
      (c : Fin D → ArcZ), ∀ n, gV hd J (E n) = autoValZ u A c n)
    (hlow : ∃ B : ℤ, ∀ n, ArcZ.fin B ≤ gV hd J (E n))
    (hU : ∀ ρ ∈ U, WeakA (gevA J ρ.lhs) (gevA J ρ.rhs))
    (hP : ∀ π' ∈ P, WeakTop hd (gevA J π'.lhs) (gevA J π'.rhs)) :
    ¬ StrictTop hd (gevA J π.lhs) (gevA J π.rhs) :=
  simulation_family_arcZ M hTW hUse E U P π ha hd J hb hlow hU hP

end Sim

/-! ## Section 6: The value-level core -/

section MinIdealSec

open MinIdeal

/-- **Lemma 6.2** (idempotents of the minimal ideal: (1)–(4) and the strongly connected case). -/
theorem paper_lem_6_2 {Q : Type*} [Finite Q] (B₀ B₁ : BRel Q) {K : Set (BRel Q)}
    (hK : IsMinIdeal (Submonoid.closure ({B₀, B₁} : Set (BRel Q))) K) {E : BRel Q}
    (hEK : E ∈ K) (hE : E * E = E) :
    (∀ X ∈ Submonoid.closure ({B₀, B₁} : Set (BRel Q)), InH E (E * X * E)) ∧
    (∀ a b, E a b → ∃ c, E c c ∧ E a c ∧ E c b) ∧
    (∀ k k' (hk : E k k) (hk' : E k' k'), cls hE k hk = cls hE k' hk' → E k = E k') ∧
    (∀ s b, E s b ↔ ∃ i, Hits hE s i ∧ beta hE i b) ∧
    (∀ i k (hk : E k k), beta hE i k ↔ i ≤ cls hE k hk) ∧
    (∀ X ∈ Submonoid.closure ({B₀, B₁} : Set (BRel Q)),
      ∃ π : Cls E hE ≃o Cls E hE, ∀ q (hq : E q q), (E * X * E) q = beta hE (π (cls hE q hq))) ∧
    ((∀ x y, Relation.ReflTransGen (fun a b => B₀ a b ∨ B₁ a b) x y) →
      (∀ i j : Cls E hE, i ≤ j → i = j) ∧
      (∀ i k (hk : E k k), beta hE i k ↔ cls hE k hk = i)) :=
  lemma_56_5_1 B₀ B₁ hK hEK hE

/-- The premise of Lemma 6.2 (existence of a minimal ideal and of an idempotent in it; cited in the formal status line of Lemma 6.2). -/
theorem paper_lem_6_2_exists {Q : Type*} [Finite Q] (B₀ B₁ : BRel Q) :
    ∃ K, IsMinIdeal (Submonoid.closure ({B₀, B₁} : Set (BRel Q))) K ∧ ∃ E ∈ K, E * E = E :=
  exists_minIdeal_idem B₀ B₁

/-- **Lemma 6.3** (transport). -/
theorem paper_lem_6_3 {Q : Type*} [Finite Q] (B₀ B₁ : BRel Q) {K : Set (BRel Q)}
    (hK : IsMinIdeal (Mon B₀ B₁) K) {E : BRel Q} (hEK : E ∈ K) (hE : E * E = E)
    {X : BRel Q} (hXM : X ∈ Mon B₀ B₁) :
    (∀ q (hq : E q q), (E * X * E) q = beta hE (piX hE X (cls hE q hq))) ∧
    (∀ I : Set (Cls E hE), act (act (betaUnion hE I) X) E = betaUnion hE (piX hE X '' I)) ∧
    (∀ I : Set (Cls E hE), IsUpperSet I → IsUpperSet (piX hE X '' I)) ∧
    (∀ j : Cls E hE, comp B₀ B₁ hE (piX hE X j) = comp B₀ B₁ hE j) ∧
    (∀ (j : Cls E hE) (k b : Q), beta hE j k → (X * E) k b → beta hE (piX hE X j) b) :=
  lemma_56_10_1 B₀ B₁ hK hEK hE hXM

/-- **Lemma 6.3** (stay). -/
theorem paper_lem_6_3_stay {Q : Type*} [Finite Q] (B₀ B₁ : BRel Q) {K : Set (BRel Q)}
    (hK : IsMinIdeal (Mon B₀ B₁) K) {E : BRel Q} (hEK : E ∈ K) (hE : E * E = E) {a b : Q}
    (hab' : Reach B₀ B₁ a b ∧ Reach B₀ B₁ b a) (hab : E a b) {S : Set Q} (ha : a ∈ S) :
    ∃ c, ∃ hc : E c c, E a c ∧ E c b ∧
      a ∈ comp B₀ B₁ hE (cls hE c hc) ∧ b ∈ comp B₀ B₁ hE (cls hE c hc) ∧
      cls hE c hc ∈ hitSet hE S ∧ beta hE (cls hE c hc) b :=
  corollary_56_10_2 B₀ B₁ hK hEK hE hab' hab ha

/-- **Lemma 6.5** (upper bound from window frequencies). -/
theorem paper_lem_6_5 {D : ℕ} (A : Interp D) (u : Fin D → Arc) {K : Set (BRel (Fin D))}
    (hK : IsMinIdeal (Mon (B0 A) (B1 A)) K) {E : BRel (Fin D)} (hEK : E ∈ K) (hE : E * E = E)
    (us : Word) (hus : IsDigits us) (hEus : suppRel (ev A us) = E) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∃ δ : ℚ, 0 < δ ∧ ∃ Cu : ℝ,
      ∀ (w : Word) (P : List Upper.Seg) (T : ℕ), IsDigits w → Upper.GoodPartition w P ε J δ →
        w.length ≤ 2 * T → T ≤ w.length → us.length ≤ T →
        window w (T - us.length) us.length = us →
        ∀ (b : Fin D) (v : ℕ), vecAfter u A (w.take T) b = Arc.fin v →
          (v : ℝ) ≤ (Upper.rhoB hE A (hitSet hE (suppV (vecAfter u A (w.take (T - us.length))))) b
            + C₁ * ε) * T + Cu :=
  Upper.lemma_56_11_1 A u hK hEK hE us hus hEus

open Classical in
/-- **Lemma 6.6** (lower bound for sequences made of concatenated intervals close to uniform, from `HSP`). -/
theorem paper_lem_6_6 (hSP : HSP) {D : ℕ} (A : Interp D) (u : Fin D → Arc)
    {K : Set (BRel (Fin D))} (hK : IsMinIdeal (Mon (B0 A) (B1 A)) K) {E : BRel (Fin D)}
    (hEK : E ∈ K) (hE : E * E = E) (ustar : Word) (hus : IsDigits ustar)
    (huE : suppRel (ev A ustar) = E) (y z : Word) (hy : IsDigits y) (hyu : ustar <:+ y) (G : ℕ) :
    ∃ Cst : ℝ, ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L₁ L₂ : ℕ, L₀ ≤ L₁ → L₀ ≤ L₂ →
      ∀ {ι : Type*} (X : Finset ι) (g₀ g₁ B₁ B₂ : ι → Word) (δ₁ δ₂ : ℝ),
        (∀ x ∈ X, (g₀ x).length ≤ G) → (∀ x ∈ X, IsDigits (g₁ x) ∧ (g₁ x).length ≤ G) →
        (∀ x ∈ X, B₁ x ∈ wordsOfLen L₁) → (∀ x ∈ X, B₂ x ∈ wordsOfLen L₂) →
        Lower.TVClose X B₁ L₁ δ₁ → Lower.TVClose X B₂ L₂ δ₂ →
        (1 - δ₁ - δ₂ - ε) * X.card ≤ ((X.filter (fun x =>
          Lower.LowerAt u A hE ustar z ε Cst (g₀ x ++ B₁ x ++ g₁ x ++ B₂ x ++ y ++ z))).card : ℝ) :=
  Lower.lemma_56_11_2 hSP A u hK hEK hE ustar hus huE y z hy hyu G

end MinIdealSec

/-- **Proposition 6.7** (uses of the left-end rules). -/
theorem paper_prop_6_7_left : HLeftUse := hLeftUse

/-- **Theorem 6.8** (assembly: `AutoCore` from the three hypotheses in finite form). -/
theorem paper_thm_6_8 : HSP → HTerrasWin → HLeftUse → AutoCore := autoCore_of_hyps

/-! ## Section 7: Transfer to $\mathcal H$ and $R_H$ -/

/-- **Lemma 7.4** (the canonical derivations of $R_H$ are the liftings of those of $\mathcal H$). -/
theorem paper_lem_7_4 (n : ℕ) : RH.canDerivRH n = (HTPDB.canDerivH n).flatMap RH.liftRH :=
  RH.canDerivRH_eq n

/-- Comparison of the numbers of uses, from Lemma 7.4 (cited in the formal status line of Lemma 7.4). -/
theorem paper_lem_7_4_count : RH.SpecCountRH := RH.specCountRH

/-- **Proposition 7.5** (the `AutoCore` of $R_H$ from the `AutoCore` of $H$). -/
theorem paper_prop_7_5 : RH.SpecCountRH → HTPDB.AutoCoreH → RH.AutoCoreRH :=
  RH.autoCoreRH_of_autoCoreH

/-! ## Section 8: Transformations before arctic reduction pairs -/

/-- **Corollary 8.1** (non-increase on family orbits suffices). -/
theorem paper_cor_8_1 (M : Gen.BlockModel) (cd : ℕ → List Rule) (ρ : Rule) (hSP : HSP)
    (hTW : Gen.HTerrasWinR M.R) (hU : Gen.HUseR M.f M.R M.steps cd ρ) :
    Gen.AutoRuleG M.f (DPGen.famDom M) cd ρ :=
  DPGen.autoRuleG_family M cd ρ hSP hTW hU

/-! ## Appendix B: Probabilistic tools -/

/-- **Theorem B.1** (reduction to expected minimal rates). -/
theorem paper_thm_B_1 : MinRate → HSP := hsp_of_minRate

/-- Theorem B.1 for a single interpretation (cited in the formal status line of Theorem B.1). -/
theorem paper_thm_B_1_at {D : ℕ} (A : Interp D) (C S : Finset (Fin D)) (hMR : MinRateAt A C) :
    HSPAt A C S :=
  hspAt_of_minRateAt A C S hMR

/-- **Proposition B.2** (sharpness). -/
theorem paper_prop_B_2 {D : ℕ} {A : Interp D} {C : Finset (Fin D)} (hND : NeverDies A C C)
    {K : ℕ} (hK : 1 ≤ K) : ((avgMinCap A C K : ℚ) : ℝ) / K ≤ rate A C :=
  hsp_avgMinCap_le_rate hND hK

/-- **Theorem B.3** (`MinRate`, without Kingman's theorem). -/
theorem paper_thm_B_3 : MinRate := minRate_holds

/-- The core of the proof of Theorem B.3 (the spread rate is 0; cited in the formal status line of Theorem B.3). -/
theorem paper_thm_B_3_spr {D : ℕ} {A : Interp D} {C : Finset (Fin D)} (hSC : StrongConnIn A C)
    (hND : NeverDies A C C) : sprRate A C = 0 :=
  hsp_sprRate_zero hSC hND

/-- **Corollary B.4** (`HSP`). -/
theorem paper_cor_B_4 : HSP := hsp_holds

/-- **Theorem B.7** (top digits of Terras residues, `HKeyTop`). -/
theorem paper_thm_B_7 : HKeyTop := hKeyTop

/-- **Theorem B.8** (window frequencies, `HTerrasWin`). -/
theorem paper_thm_B_8 : HTerrasWin := hTerrasWin

/-- Theorem B.8 from Theorem B.7 (cited in the formal status line of Theorem B.8). -/
theorem paper_thm_B_8_of_key : HKeyTop → HTerrasWin := hTerrasWin_of_key

/-- **Proposition B.9** (equidistribution of the walk of block boundary points). -/
theorem paper_prop_B_9 (lo hi : ℝ) (h0 : 0 ≤ lo) (hlh : lo < hi) (h1 : hi ≤ 1) :
    ∃ c : ℚ, 0 < c ∧ ∀ (β₀ : List Bool) (ε : ℚ), 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀,
      1 - ε ≤ Prσ β₀ k (fun β => ∀ φ : ℝ, (c : ℝ) * k ≤
        (((Finset.range β.length).filter (fun i =>
          lo ≤ Int.fract ((oddPrefix β i : ℝ) * Real.logb 2 3 + φ) ∧
          Int.fract ((oddPrefix β i : ℝ) * Real.logb 2 3 + φ) < hi)).card : ℝ)) :=
  walk_equid lo hi h0 hlh h1

end Collatz.Arctic.Paper
