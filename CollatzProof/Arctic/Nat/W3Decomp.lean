/-
# Natural-number interpretations of 𝒯, entry file: the statement of the decomposition data `DecompData` (Definition 12.9)

**Only the statement** of the structure is frozen here (the proof is in the later files `W3DecompProof*.lean`). It is written to fit
the use of Definition 12.9 and Lemma 12.10 (skeletons, labels, product form), of degeneration (Lemma 12.22) and of Propositions 12.27
and 12.28, in the case where **all components are 0/1** and for **any occurrence of `u♯`**. Downstream (the finite set of configurations,
`coef`, `deg`, the upper bound at the starting point, the lower bound at the end point) uses the forms (a)(b)(c) proved here and
**the lower bound `t₀ γ ≥ |τ'| + |u♯|` for the position of the first long sojourn**. This lower bound is not in the frozen statement
`DecompStmt`; it is added by `DecompStmtT0` (`W3hMain.lean`) and satisfied by `decompData` (`decompStmtT0` in `W3hCore.lean`). It is
needed in the upper bound at the starting point: the admissible positions `p ≥ t₀ γ` then satisfy `p ≥ |u♯|`, so the forward state lies in
the class of `e` and the degeneration lemma (Lemma 12.22) applies (remark on the lower bound for `t₀`, Section 12.3; corrected after internal review).

* **Point words** (§1): `ω = τ' (u♯)^R · m · y'' (u♯)^R z` (`fullW`). The top part `τ = τ'(u♯)^R` (`topW`) and the shared low part
  `y = y''(u♯)^R z` (`tailW`) are fixed; the middle part `m` is arbitrary. The configuration time `T` is the end of `(u♯)^R` in `y` (`posT`).
  `κ` depends only on the forward state `s_T = μ(ω_{(0,T]})` at `T` (`t₁` is the end of a copy in `(u♯)^R`, so `s_{t₁} = s_T`).
* **Admissible positions and ranges** (§2): `Adm s t₀ t₁ p r` (`r_k ≥ 1`, `t₀ ≤ p_1`, `p_k + r_k ≤ p_{k+1}`, `p_s + r_s ≤ t₁`).
  This is the indicator `1[p_{k+1} ≥ p_k + R(π_k)]` of an earlier written form of the main identity, with the range `r_k` as a summation variable.
* **Detour weights** (§2): `ξ_{γ,k,λ}(r, p) = [s_p = labS λ] · g_{γ,k,λ}(r, ω_{(p, p+r]})` (`xiOf`; in the written form `ξ = [x_p = x] g(future digits)`,
  where `x_p` is the forward state `s_p = μ(ω_{(0,p]})`).
* **`DecompData`** (§3): skeletons `Γ` (finite), degree `deg`, `t₀`, `t₁`, labels `Lab` (finite), `κ`, `g`, the properties of `g`
  (window length `g_len`, polynomial bound `g_poly` (added after internal review), long windows without `u♯` `g_free` (input of the tail bounds)), and the **main identity**
  `spec` (the identity of Definition 12.9: the exact splitting of the sum of the weights of paths).
* **The form of the statement** (§3): `DecompStmt` (if all components are 0/1, `Sharp` holds and `R ≥ |Q|`, then `DecompData` exists for all `τ', y'', z`).
  It is proved as `decompStmt` (Proposition 12.11).
* **The forms used downstream** (§4, proved here): (a) the **upper bound** `term_le_upper` (dropping the constraints on the ranges; `p` runs over strictly increasing tuples in `[t₀, t₁)`,
  `Ξ := Σ_r ξ(r, ·)`), (b) the **lower bound** `lower_le_term` (restricted to ranges `≤ M` and gaps `≥ M`), (c) **equality in degree 0**
  `term_of_deg_zero` (the term is `κ` itself). Together: `aval_le_upper`, `lower_le_aval`, `aval_eq_deg0`.
* **The DFA of forward states** (§5, the interface to the laws of large numbers of Section 12.4): `muStepB` reading `Bool` (`s ↦ s μ(b)`),
  `run_muStepB` (`run s (ω.map f2b) = s μ(ω)`; `f2b b = decide (b = 1)` is the same expression as `f2b` of `DfaLlnAvg.lean`),
  `muStepB_recurrent` (if `s ∈ \mathcal K`, then `s` is recurrent: the hypothesis `Recurrent` of Section 12.4). The state `μ(ω_{(0,p]})` of `ξ` is
  the state of this DFA reached from `1`, and after `τ` it lies in `\mathcal K` (`Sharp.muZ_mem_K`).
-/
import CollatzProof.Arctic.Nat.W3Stay
import CollatzProof.Arctic.Dfa

namespace Collatz.Arctic.NatQ5.W3c

open Collatz.Arctic Collatz.Arctic.NatQ5 Matrix
open Collatz.Arctic.MinIdeal (BRel)

set_option linter.unusedSectionVars false

/-! ## §1 Point words -/

section Words

/-- The top part `τ = τ'(u♯)^R` (Section 12.3). -/
def topW (u τ' : List (Fin 2)) (R : ℕ) : List (Fin 2) := τ' ++ (List.replicate R u).flatten

/-- The shared low part `y = y''(u♯)^R z` (the low part of Section 12.3; its part `y''(u♯)^R` ends with `(u♯)^R`). -/
def tailW (u y'' z : List (Fin 2)) (R : ℕ) : List (Fin 2) := y'' ++ (List.replicate R u).flatten ++ z

/-- The point word `ω = τ m y`. -/
def fullW (u τ' y'' z m : List (Fin 2)) (R : ℕ) : List (Fin 2) := topW u τ' R ++ m ++ tailW u y'' z R

/-- The configuration time `T`: the end of `(u♯)^R` in the shared part. -/
def posT (u τ' y'' m : List (Fin 2)) (R : ℕ) : ℕ := (topW u τ' R).length + m.length + y''.length + R * u.length

theorem length_topW (u τ' : List (Fin 2)) (R : ℕ) : (topW u τ' R).length = τ'.length + R * u.length := by
  simp [topW, List.length_flatten, List.map_replicate, List.sum_replicate]

theorem length_tailW (u y'' z : List (Fin 2)) (R : ℕ) :
    (tailW u y'' z R).length = y''.length + R * u.length + z.length := by
  simp [tailW, List.length_flatten, List.map_replicate, List.sum_replicate]; omega

theorem length_fullW (u τ' y'' z m : List (Fin 2)) (R : ℕ) :
    (fullW u τ' y'' z m R).length = (topW u τ' R).length + m.length + (tailW u y'' z R).length := by
  simp only [fullW, List.length_append]

end Words

/-! ## §2 Admissible positions and ranges, detour weights -/

section Adm

/-- **Admissible positions and ranges** (the range of summation in Definition 12.9): ranges are at least 1, the first position is at least `t₀`, the next long
sojourn ends no earlier than the end of the range (`p_k + r_k ≤ p_{k+1}`), and the range of the last detour ends by `t₁`. -/
def Adm (s t0 t1 : ℕ) (p r : Fin s → ℕ) : Prop :=
  (∀ k, 1 ≤ r k) ∧ (∀ k : Fin s, k.val = 0 → t0 ≤ p k) ∧
    (∀ k k' : Fin s, k'.val = k.val + 1 → p k + r k ≤ p k') ∧ (∀ k : Fin s, k.val + 1 = s → p k + r k ≤ t1)

open Classical in
/-- The finite set of admissible `(p, r)` (positions and ranges at most `N`). -/
noncomputable def admSet (s t0 t1 N : ℕ) : Finset ((Fin s → ℕ) × (Fin s → ℕ)) :=
  (Fintype.piFinset (fun _ : Fin s => Finset.range (N + 1)) ×ˢ
    Fintype.piFinset (fun _ : Fin s => Finset.range (N + 1))).filter (fun pr => Adm s t0 t1 pr.1 pr.2)

open Classical in
/-- The set of positions for the upper bound: strictly increasing tuples in `[a, b)`. -/
noncomputable def incrSet (s a b : ℕ) : Finset (Fin s → ℕ) :=
  (Fintype.piFinset (fun _ : Fin s => Finset.range b)).filter (fun p => StrictMono p ∧ ∀ k, a ≤ p k)

open Classical in
/-- The set of positions for the lower bound: the first is at least `a`, the gaps are at least `M`, and the last is at most `b - M`. -/
noncomputable def gapSet (s a b M : ℕ) : Finset (Fin s → ℕ) :=
  (Fintype.piFinset (fun _ : Fin s => Finset.range b)).filter (fun p =>
    (∀ k : Fin s, k.val = 0 → a ≤ p k) ∧ (∀ k k' : Fin s, k'.val = k.val + 1 → p k + M ≤ p k') ∧
      (∀ k : Fin s, k.val + 1 = s → p k + M ≤ b))

/-- The indicator of a proposition (classical decision). -/
noncomputable def ind (P : Prop) : ℕ := @ite ℕ P (Classical.propDecidable P) 1 0

theorem ind_le_one (P : Prop) : ind P ≤ 1 := by unfold ind; split_ifs <;> simp

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (A : ValAuto Q)

/-- **Detour weight** `ξ(r, p) = [s_p = labS λ] · g_λ(r, ω_{(p,p+r]})` (`s_p = μ(ω_{(0,p]})`). -/
noncomputable def xiOf {Lab : Type} (labS : Lab → BRel (ZIdx A)) (g : Lab → ℕ → List (Fin 2) → ℕ) (l : Lab)
    (r : ℕ) (ω : List (Fin 2)) (p : ℕ) : ℕ :=
  ind (muZ A (ω.take p) = labS l) * g l r ((ω.drop p).take r)

/-- **The term of one skeleton**: `Σ_λ κ(s_T; λ) Σ_{(p, r) admissible} Π_k ξ_{k, λ_k}(r_k, p_k)`. -/
noncomputable def termOf {Lab : Type} [Fintype Lab] (labS : Lab → BRel (ZIdx A)) (s : ℕ)
    (κ : BRel (ZIdx A) → (Fin s → Lab) → ℕ) (g : Fin s → Lab → ℕ → List (Fin 2) → ℕ) (t0 t1 : ℕ)
    (sT : BRel (ZIdx A)) (ω : List (Fin 2)) : ℕ :=
  ∑ l : Fin s → Lab, κ sT l * ∑ pr ∈ admSet s t0 t1 ω.length,
    ∏ k : Fin s, xiOf A labS (g k) (l k) (pr.2 k) ω (pr.1 k)

end Adm

/-! ## §3 `DecompData` -/

section Data

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- **Decomposition data** (Definition 12.9 of the paper) for the automaton `A` (all components 0/1), `u♯` (`u`), the top part `τ'(u♯)^R`
and the shared part `y''(u♯)^R z`:

* `Γ`: the **skeletons** (finite; in the written form a skeleton `γ` records `t₀`, `t₁`, the sequence of components of the long sojourns passed,
  the entry and exit indices of each sojourn, the types of the detours, and the top and bottom parts). `deg γ`: the number of detours (the **degree**).
* `t0 γ`: the end of the copy in the top part that the first long sojourn contains (an absolute position, at most `|τ|`). `t1 γ`: the end of the copy
  in the shared part that the last long sojourn contains (a position in `y`; the absolute position is `|τ| + |m| + t1 γ`).
* `Lab`: the **labels** (finite; in the written form `λ_k = (x_{p_k}, i'_{k+1}, s_{p'_k}, A_k)`), `labS λ`: the forward-state component of a label.
* `κ γ s_T λ`: non-negative coefficients (the product of the weights of the top and bottom parts and the indicators `[Θ(…)_{i'i}]` of the long sojourns, determined by pairs of adjacent labels).
* `g γ k λ r v`: the total weight of the detours (the `k`-th, with label `λ`) whose range is exactly `r`, as a function of the window `v = ω_{(p,p+r]}`.
* `g_len`: if `g` is positive, the window has length `r` (positions where the window is cut off at the end of the word do not contribute).
* `g_poly`: `g ≤ c_P (r + 1)^{d_P}` (added after internal review; from `entry_poly`).
* `g_free`: if `g` is positive, the window has a part of length `ℓ ≥ r / c_W - 1` that does not contain `u♯` (the sojourns of a detour do not contain `u♯`,
  and the tail `(p', r)` of the range lies before the first occurrence; the input of the tail bounds of Section 12.7).
* `spec`: the **main identity** (the identity of Definition 12.9). For every `m`, `V(ω) = Σ_γ term γ` (the value `V` is `aval`). -/
structure DecompData (A : ValAuto Q) (u τ' y'' z : List (Fin 2)) (R : ℕ) where
  Γ : Type
  finΓ : Fintype Γ
  deg : Γ → ℕ
  t0 : Γ → ℕ
  t1 : Γ → ℕ
  t0_le : ∀ γ, t0 γ ≤ (topW u τ' R).length
  t1_le : ∀ γ, t1 γ ≤ y''.length + R * u.length
  Lab : Type
  finLab : Fintype Lab
  labS : Lab → BRel (ZIdx A)
  κ : (γ : Γ) → BRel (ZIdx A) → (Fin (deg γ) → Lab) → ℕ
  g : (γ : Γ) → Fin (deg γ) → Lab → ℕ → List (Fin 2) → ℕ
  g_len : ∀ γ k l r v, g γ k l r v ≠ 0 → v.length = r
  cP : ℕ
  dP : ℕ
  g_poly : ∀ γ k l r v, g γ k l r v ≤ cP * (r + 1) ^ dP
  cW : ℕ
  g_free : ∀ γ k l r v, g γ k l r v ≠ 0 →
    ∃ a ℓ, a + ℓ ≤ r ∧ r ≤ cW * (ℓ + 1) ∧ ¬ u <:+: (v.drop a).take ℓ
  spec : ∀ m : List (Fin 2), aval A (fullW u τ' y'' z m R) =
    @Finset.sum Γ ℕ _ (@Finset.univ Γ finΓ) fun γ =>
      @termOf Q _ _ A Lab finLab labS (deg γ) (κ γ) (g γ) (t0 γ) ((topW u τ' R).length + m.length + t1 γ)
        (muZ A ((fullW u τ' y'' z m R).take (posT u τ' y'' m R))) (fullW u τ' y'' z m R)

/-- **The target** (Proposition 12.11): if all components are 0/1, `u♯` is `Sharp` and `R ≥ |Q|`, then decomposition data exist for every top part `τ'(u♯)^R`
and every shared part `y''(u♯)^R z`. -/
def DecompStmt : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (A : ValAuto Q), (∀ C, IsComp A C → ZeroOne A C) →
    ∀ (K : Set (BRel (ZIdx A))) (u : List (Fin 2)) (e : BRel (ZIdx A)), Sharp A K u e →
      ∀ R, Fintype.card Q ≤ R → ∀ τ' y'' z : List (Fin 2), Nonempty (DecompData A u τ' y'' z R)

end Data

/-! ## §4 The forms used downstream -/

section Use

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (A : ValAuto Q)

/-- The total detour weight `Ξ(p) := Σ_{r ≤ N} ξ(r, p)` (used for the upper bound). -/
noncomputable def XiOf {Lab : Type} (labS : Lab → BRel (ZIdx A)) (g : Lab → ℕ → List (Fin 2) → ℕ) (l : Lab)
    (ω : List (Fin 2)) (p : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (ω.length + 1), xiOf A labS g l r ω p

/-- The weight of the detours of range at most `M`, `Ξ^{(M)}(p) := Σ_{1 ≤ r ≤ M} ξ(r, p)` (used for the lower bound; `Ξ^{(M)}` of Lemma 12.10). -/
noncomputable def XiLe {Lab : Type} (labS : Lab → BRel (ZIdx A)) (g : Lab → ℕ → List (Fin 2) → ℕ) (l : Lab)
    (M : ℕ) (ω : List (Fin 2)) (p : ℕ) : ℕ :=
  ∑ r ∈ Finset.Icc 1 M, xiOf A labS g l r ω p

theorem adm_strictMono {s t0 t1 : ℕ} {p r : Fin s → ℕ} (h : Adm s t0 t1 p r) : StrictMono p := by
  have hstep : ∀ k k' : Fin s, k'.val = k.val + 1 → p k < p k' := fun k k' hk => by
    have := h.2.2.1 k k' hk
    have := h.1 k
    omega
  have key : ∀ n (a b : Fin s), b.val = a.val + n + 1 → p a < p b := by
    intro n
    induction n with
    | zero => intro a b h; exact hstep a b (by omega)
    | succ n ih =>
      intro a b h
      have hb1 : b.val - 1 < s := by omega
      exact (ih a ⟨b.val - 1, hb1⟩ (by show b.val - 1 = a.val + n + 1; omega)).trans
        (hstep _ b (by show b.val = (b.val - 1) + 1; omega))
  intro a b hab
  have : a.val < b.val := hab
  exact key (b.val - a.val - 1) a b (by omega)

theorem adm_ge {s t0 t1 : ℕ} {p r : Fin s → ℕ} (h : Adm s t0 t1 p r) (k : Fin s) : t0 ≤ p k := by
  have h0 : 0 < s := by have := k.2; omega
  have hmono := adm_strictMono h
  have := h.2.1 ⟨0, h0⟩ rfl
  exact this.trans (hmono.monotone (show (⟨0, h0⟩ : Fin s) ≤ k from by simp [Fin.le_def]))

theorem adm_lt {s t0 t1 : ℕ} {p r : Fin s → ℕ} (h : Adm s t0 t1 p r) (k : Fin s) : p k < t1 := by
  have h0 : s - 1 < s := by have := k.2; omega
  have hmono := adm_strictMono h
  have hl := h.2.2.2 ⟨s - 1, h0⟩ (by simp; omega)
  have hr := h.1 ⟨s - 1, h0⟩
  have := hmono.monotone (show k ≤ (⟨s - 1, h0⟩ : Fin s) from by simp [Fin.le_def]; omega)
  omega

/-- **(a) Upper bound** (Lemma 12.10 (i)): dropping the constraints on the ranges, the term is at most `Σ_λ κ Σ_{t₀ ≤ p₁ < ⋯ < p_s < t₁} Π_k Ξ_{λ_k}(p_k)`. -/
theorem termOf_le_upper {Lab : Type} [Fintype Lab] (labS : Lab → BRel (ZIdx A)) (s : ℕ)
    (κ : BRel (ZIdx A) → (Fin s → Lab) → ℕ) (g : Fin s → Lab → ℕ → List (Fin 2) → ℕ) (t0 t1 : ℕ)
    (sT : BRel (ZIdx A)) (ω : List (Fin 2)) (_ht1 : t1 ≤ ω.length) :
    termOf A labS s κ g t0 t1 sT ω ≤
      ∑ l : Fin s → Lab, κ sT l * ∑ p ∈ incrSet s t0 t1, ∏ k : Fin s, XiOf A labS (g k) (l k) ω (p k) := by
  classical
  unfold termOf
  refine Finset.sum_le_sum fun l _ => Nat.mul_le_mul_left _ ?_
  -- expand the right-hand side into a sum over `(p, r)`
  have hexp : ∀ p : Fin s → ℕ, ∏ k : Fin s, XiOf A labS (g k) (l k) ω (p k) =
      ∑ r ∈ Fintype.piFinset (fun _ : Fin s => Finset.range (ω.length + 1)),
        ∏ k : Fin s, xiOf A labS (g k) (l k) (r k) ω (p k) := by
    intro p
    unfold XiOf
    exact Finset.prod_univ_sum (fun _ => Finset.range (ω.length + 1)) (fun k r => xiOf A labS (g k) (l k) r ω (p k))
  simp_rw [hexp]
  rw [← Finset.sum_product']
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _)
  intro pr hpr
  unfold admSet at hpr
  rw [Finset.mem_filter, Finset.mem_product] at hpr
  obtain ⟨⟨_, hr⟩, hadm⟩ := hpr
  rw [Finset.mem_product]
  refine ⟨?_, hr⟩
  unfold incrSet
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun k => Finset.mem_range.2 (adm_lt hadm k), adm_strictMono hadm, adm_ge hadm⟩

/-- **(b) Lower bound** (Lemma 12.10 (ii)): restricted to detours of range at most `M` and to tuples of positions with gaps at least `M`, the term is
at least `Σ_λ κ Σ_{p ∈ gapSet} Π_k Ξ^{(M)}_{λ_k}(p_k)`. -/
theorem lower_le_termOf {Lab : Type} [Fintype Lab] (labS : Lab → BRel (ZIdx A)) (s : ℕ)
    (κ : BRel (ZIdx A) → (Fin s → Lab) → ℕ) (g : Fin s → Lab → ℕ → List (Fin 2) → ℕ) (t0 t1 : ℕ)
    (sT : BRel (ZIdx A)) (ω : List (Fin 2)) (ht1 : t1 ≤ ω.length) (M : ℕ) :
    ∑ l : Fin s → Lab, κ sT l * ∑ p ∈ gapSet s t0 t1 M, ∏ k : Fin s, XiLe A labS (g k) (l k) M ω (p k) ≤
      termOf A labS s κ g t0 t1 sT ω := by
  classical
  unfold termOf
  refine Finset.sum_le_sum fun l _ => Nat.mul_le_mul_left _ ?_
  have hexp : ∀ p : Fin s → ℕ, ∏ k : Fin s, XiLe A labS (g k) (l k) M ω (p k) =
      ∑ r ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc 1 M),
        ∏ k : Fin s, xiOf A labS (g k) (l k) (r k) ω (p k) := by
    intro p
    unfold XiLe
    exact Finset.prod_univ_sum (fun _ => Finset.Icc 1 M) (fun k r => xiOf A labS (g k) (l k) r ω (p k))
  simp_rw [hexp]
  rw [← Finset.sum_product']
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _)
  intro pr hpr
  rw [Finset.mem_product] at hpr
  obtain ⟨hp, hr⟩ := hpr
  unfold gapSet at hp
  rw [Finset.mem_filter, Fintype.mem_piFinset] at hp
  obtain ⟨hpb, h0, hgap, hlast⟩ := hp
  rw [Fintype.mem_piFinset] at hr
  have hrM : ∀ k, 1 ≤ pr.2 k ∧ pr.2 k ≤ M := fun k => Finset.mem_Icc.1 (hr k)
  unfold admSet
  rw [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset]
  refine ⟨⟨fun k => Finset.mem_range.2 (by have := Finset.mem_range.1 (hpb k); omega), fun k => ?_⟩,
    fun k => (hrM k).1, h0, fun k k' hk => ?_, fun k hk => ?_⟩
  · have hl := hlast ⟨s - 1, by have := k.2; omega⟩ (by simp; have := k.2; omega)
    have := (hrM k).2
    have := Finset.mem_range.1 (hpb ⟨s - 1, by have := k.2; omega⟩)
    exact Finset.mem_range.2 (by omega)
  · have := hgap k k' hk; have := (hrM k).2; omega
  · have := hlast k hk; have := (hrM k).2; omega

/-- **(c) Equality in degree 0** (Lemma 12.10 (iii)): the term of a skeleton without detours is `κ(s_T)` itself. -/
theorem termOf_of_deg_zero {Lab : Type} [Fintype Lab] (labS : Lab → BRel (ZIdx A)) {s : ℕ} (hs : s = 0)
    (κ : BRel (ZIdx A) → (Fin s → Lab) → ℕ) (g : Fin s → Lab → ℕ → List (Fin 2) → ℕ) (t0 t1 : ℕ)
    (sT : BRel (ZIdx A)) (ω : List (Fin 2)) :
    termOf A labS s κ g t0 t1 sT ω = κ sT (fun k => absurd k.2 (by omega)) := by
  classical
  subst hs
  unfold termOf
  have hf : ∀ f : Fin 0 → Lab, f = (fun k => absurd k.2 (by omega)) := fun f => funext fun k => absurd k.2 (by omega)
  have hf' : ∀ f : Fin 0 → ℕ, f = (fun k => absurd k.2 (by omega)) := fun f => funext fun k => absurd k.2 (by omega)
  rw [Fintype.sum_eq_single (fun k => absurd k.2 (by omega)) (fun f hf0 => absurd (hf f) hf0)]
  have hadm : admSet 0 t0 t1 ω.length = {((fun k => absurd k.2 (by omega)), (fun k => absurd k.2 (by omega)))} := by
    ext ⟨p, r⟩
    simp only [Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · intro _; exact ⟨hf' p, hf' r⟩
    · rintro ⟨rfl, rfl⟩
      unfold admSet
      simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset]
      exact ⟨⟨fun k => absurd k.2 (by omega), fun k => absurd k.2 (by omega)⟩, fun k => absurd k.2 (by omega),
        fun k => absurd k.2 (by omega), fun k => absurd k.2 (by omega), fun k => absurd k.2 (by omega)⟩
  rw [hadm, Finset.sum_singleton]
  simp

/-! ### Application to `DecompData` -/

variable {A} {u τ' y'' z : List (Fin 2)} {R : ℕ}

instance (D : DecompData A u τ' y'' z R) : Fintype D.Γ := D.finΓ
instance (D : DecompData A u τ' y'' z R) : Fintype D.Lab := D.finLab

/-- The term of the skeleton `γ` (on the point word `fullW … m …`). -/
noncomputable def DecompData.term (D : DecompData A u τ' y'' z R) (m : List (Fin 2)) (γ : D.Γ) : ℕ :=
  termOf A D.labS (D.deg γ) (D.κ γ) (D.g γ) (D.t0 γ) ((topW u τ' R).length + m.length + D.t1 γ)
    (muZ A ((fullW u τ' y'' z m R).take (posT u τ' y'' m R))) (fullW u τ' y'' z m R)

/-- The forward state `s_T`. -/
noncomputable def DecompData.sT (_D : DecompData A u τ' y'' z R) (m : List (Fin 2)) : BRel (ZIdx A) :=
  muZ A ((fullW u τ' y'' z m R).take (posT u τ' y'' m R))

/-- `t₁` as an absolute position. -/
def DecompData.t1abs (D : DecompData A u τ' y'' z R) (m : List (Fin 2)) (γ : D.Γ) : ℕ :=
  (topW u τ' R).length + m.length + D.t1 γ

theorem DecompData.aval_eq (D : DecompData A u τ' y'' z R) (m : List (Fin 2)) :
    aval A (fullW u τ' y'' z m R) = ∑ γ, D.term m γ := D.spec m

theorem DecompData.t1abs_le (D : DecompData A u τ' y'' z R) (m : List (Fin 2)) (γ : D.Γ) :
    D.t1abs m γ ≤ (fullW u τ' y'' z m R).length := by
  have := D.t1_le γ
  rw [length_fullW, length_tailW]
  unfold DecompData.t1abs
  omega

/-- **(a)** The upper bound for each skeleton. -/
theorem DecompData.term_le_upper (D : DecompData A u τ' y'' z R) (m : List (Fin 2)) (γ : D.Γ) :
    D.term m γ ≤ ∑ l : Fin (D.deg γ) → D.Lab, D.κ γ (D.sT m) l *
      ∑ p ∈ incrSet (D.deg γ) (D.t0 γ) (D.t1abs m γ),
        ∏ k : Fin (D.deg γ), XiOf A D.labS (D.g γ k) (l k) (fullW u τ' y'' z m R) (p k) :=
  termOf_le_upper A _ _ _ _ _ _ _ _ (D.t1abs_le m γ)

/-- **(b)** The lower bound for each skeleton. -/
theorem DecompData.lower_le_term (D : DecompData A u τ' y'' z R) (m : List (Fin 2)) (γ : D.Γ) (M : ℕ) :
    ∑ l : Fin (D.deg γ) → D.Lab, D.κ γ (D.sT m) l *
      ∑ p ∈ gapSet (D.deg γ) (D.t0 γ) (D.t1abs m γ) M,
        ∏ k : Fin (D.deg γ), XiLe A D.labS (D.g γ k) (l k) M (fullW u τ' y'' z m R) (p k) ≤ D.term m γ :=
  lower_le_termOf A _ _ _ _ _ _ _ _ (D.t1abs_le m γ) M

/-- **(c)** The term of a skeleton of degree 0 is `κ(s_T)`. -/
theorem DecompData.term_of_deg_zero (D : DecompData A u τ' y'' z R) (m : List (Fin 2)) (γ : D.Γ)
    (h : D.deg γ = 0) : D.term m γ = D.κ γ (D.sT m) (fun k => absurd k.2 (by omega)) :=
  termOf_of_deg_zero A _ h _ _ _ _ _ _

/-- The upper bound for the value (sum over the skeletons). -/
theorem DecompData.aval_le_upper (D : DecompData A u τ' y'' z R) (m : List (Fin 2)) :
    aval A (fullW u τ' y'' z m R) ≤ ∑ γ, ∑ l : Fin (D.deg γ) → D.Lab, D.κ γ (D.sT m) l *
      ∑ p ∈ incrSet (D.deg γ) (D.t0 γ) (D.t1abs m γ),
        ∏ k : Fin (D.deg γ), XiOf A D.labS (D.g γ k) (l k) (fullW u τ' y'' z m R) (p k) := by
  rw [D.aval_eq]
  exact Finset.sum_le_sum fun γ _ => D.term_le_upper m γ

/-- The lower bound for the value (sum over the skeletons). -/
theorem DecompData.lower_le_aval (D : DecompData A u τ' y'' z R) (m : List (Fin 2)) (M : ℕ) :
    ∑ γ, ∑ l : Fin (D.deg γ) → D.Lab, D.κ γ (D.sT m) l *
      ∑ p ∈ gapSet (D.deg γ) (D.t0 γ) (D.t1abs m γ) M,
        ∏ k : Fin (D.deg γ), XiLe A D.labS (D.g γ k) (l k) M (fullW u τ' y'' z m R) (p k) ≤
      aval A (fullW u τ' y'' z m R) := by
  rw [D.aval_eq]
  exact Finset.sum_le_sum fun γ _ => D.lower_le_term m γ M

/-- If the terms of all skeletons of degree at least 1 vanish, the value is the sum of the coefficients of degree 0 (Lemma 12.10 (iii); used together with
the degeneration lemma, Lemma 12.22). -/
theorem DecompData.aval_eq_deg0 (D : DecompData A u τ' y'' z R) (m : List (Fin 2))
    (h : ∀ γ, D.deg γ ≠ 0 → D.term m γ = 0) :
    aval A (fullW u τ' y'' z m R) =
      ∑ γ ∈ Finset.univ.filter (fun γ => D.deg γ = 0), D.term m γ := by
  classical
  rw [D.aval_eq, Finset.sum_filter]
  refine Finset.sum_congr rfl fun γ _ => ?_
  split_ifs with hγ
  · rfl
  · exact h γ hγ

end Use

/-! ## §5 The DFA of forward states -/

section MuDfa

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (A : ValAuto Q)

/-- The DFA of forward states `s ↦ s μ(b)` reading `Bool` (`true` is the digit 1; the form of `Dfa.run` used in Section 12.4). -/
def muStepB (s : BRel (ZIdx A)) (b : Bool) : BRel (ZIdx A) := s * muZ A [if b then 1 else 0]

theorem run_muStepB_bool (s : BRel (ZIdx A)) (w : List Bool) :
    Dfa.run (muStepB A) s w = s * muZ A (w.map (fun b => if b then (1 : Fin 2) else 0)) := by
  induction w generalizing s with
  | nil => simp [Dfa.run, muZ_nil]
  | cons b w ih =>
    rw [Dfa.run_cons, ih, muStepB, List.map_cons, mul_assoc, ← muZ_append]; rfl

/-- `run s (ω.map f2b) = s μ(ω)` (`f2b b = decide (b = 1)`). -/
theorem run_muStepB (s : BRel (ZIdx A)) (ω : List (Fin 2)) :
    Dfa.run (muStepB A) s (ω.map (fun b => decide (b = 1))) = s * muZ A ω := by
  rw [run_muStepB_bool, List.map_map]
  congr 2
  conv_rhs => rw [← List.map_id ω]
  refine List.map_congr_left fun b _ => ?_
  fin_cases b <;> rfl

/-- **Recurrence**: if `s ∈ \mathcal K`, then `s` is a recurrent state of the DFA `muStepB` (the hypothesis `Recurrent` of Section 12.4). -/
theorem muStepB_recurrent {K : Set (BRel (ZIdx A))} (hK : MinIdeal.IsMinIdeal (muMon A) K) {s : BRel (ZIdx A)} (hs : s ∈ K) :
    Dfa.Recurrent (muStepB A) s := by
  rintro q' ⟨w, rfl⟩
  rw [run_muStepB_bool]
  obtain ⟨w', hw'⟩ := muZ_recurrent A hK hs (w.map (fun b => if b then (1 : Fin 2) else 0))
  exact ⟨w'.map (fun b => decide (b = 1)), by rw [run_muStepB, hw']⟩

/-- A detour weight is a function of the DFA state and of the following window: `ξ(r, p) = [run 1 (ω_{<p}) = labS λ] · g(r, (ω_{≥p})_{<r})`. -/
theorem xiOf_eq_run {Lab : Type} (labS : Lab → BRel (ZIdx A)) (g : Lab → ℕ → List (Fin 2) → ℕ) (l : Lab) (r : ℕ)
    (ω : List (Fin 2)) (p : ℕ) :
    xiOf A labS g l r ω p =
      ind (Dfa.run (muStepB A) 1 ((ω.take p).map (fun b => decide (b = 1))) = labS l) * g l r ((ω.drop p).take r) := by
  rw [run_muStepB, one_mul]; rfl

end MuDfa

end Collatz.Arctic.NatQ5.W3c
