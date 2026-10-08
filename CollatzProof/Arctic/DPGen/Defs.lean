/-
Lean foundation of Section 8 (Section 8.1): definitions.

Definitions for stating Lemma 5.6 (the simulation lemma) for dependency pair problems over a type `α` of symbols, and
a general form of the number of uses for stating Corollary 8.1 (non-increase on the steps of the family only).

* `GLetter α` (unmarked symbols and marked symbols `s^#`), `GDRule α` (rules and dependency pairs), `gevA` (composition of arctic linear functions;
  the form of `DPStatement.evA` with the symbol type as a parameter). The comparisons `WeakA`, `WeakTop`, `StrictTop` are those of `DPStatement`.
* `GDChain U P`: a rewrite sequence on strings, made of steps by rules of `U` (`under`, at any position) and root steps by dependency pairs
  (`root`, replacing the left-hand side of a pair of `P` by its right-hand side). The label `GLabel` records the kind of step and the rule (the number of root uses of `π` is
  `es.count (GLabel.root π)`; it is counted correctly even if a rule used below the root coincides with a dependency pair).
  In a dependency pair chain the steps by rules of `U(𝒫)` take place below the root; here the position of an `under` step is not restricted. This only weakens hypothesis (a),
  and the argument on values (steps below the root do not increase the value) does not depend on the position.
* `gV hd J w := ([w](x*))₁` (in homogeneous coordinates; by `gV_eq_apply` it equals the value of the linear function itself).
* `usesG f cnt`: the sum of the counts `cnt` at the points of an orbit segment (the form of `Gen.usesOrbitG` with the counting function as a parameter).
* `AutoUseG f dom cnt`, `HUseC f R steps cnt`: the forms of `Gen.AutoRuleG`, `Gen.HUseR` with the counting function as a parameter.
  With `cnt n := (cd n).count ρ` they are definitionally the original forms (`autoRuleG_iff_use`, `hUseR_iff_use`).
-/
import CollatzProof.Arctic.DPBridge
import CollatzProof.Arctic.Gen.Model

namespace Collatz.Arctic.DPGen

open Collatz.Arctic Collatz.Arctic.Gen Matrix

/-! ## Symbols, rules, chains -/

/-- Symbols of a dependency pair problem over the symbol type `α`: unmarked symbols and marked symbols `s^#`. -/
inductive GLetter (α : Type) where
  | plain (s : α)
  | mark (s : α)
  deriving DecidableEq, Repr

/-- Rules and dependency pairs (pairs of strings of symbols). -/
structure GDRule (α : Type) where
  lhs : List (GLetter α)
  rhs : List (GLetter α)
  deriving DecidableEq, Repr

/-- Labels of chain steps: steps by rules of `U` (`under`) and root steps by dependency pairs (`root`). -/
inductive GLabel (α : Type) where
  | under (ρ : GDRule α)
  | root (π : GDRule α)
  deriving DecidableEq, Repr

variable {α : Type}

/-- Interpretation of a string: the composition `[s_1] ∘ ⋯ ∘ [s_k]` of linear functions (the form of `DPStatement.evA` with the symbol type as a parameter). -/
def gevA {R : Type} [CommSemiring R] {d : ℕ} (J : GLetter α → AffFun R d)
    (w : List (GLetter α)) : AffFun R d :=
  w.foldr (fun s acc => (J s).comp acc) AffFun.id

/-- General chains: steps by rules of `U` (at any position `p`) and root steps by dependency pairs (left-hand side of a pair `π` of `P` to its right-hand side). -/
inductive GDChain (U P : List (GDRule α)) :
    List (GLabel α) → List (GLetter α) → List (GLetter α) → Prop
  | nil (w : List (GLetter α)) : GDChain U P [] w w
  | under {ρ : GDRule α} {es : List (GLabel α)} {v : List (GLetter α)} (p q : List (GLetter α)) :
      ρ ∈ U → GDChain U P es (p ++ ρ.rhs ++ q) v →
        GDChain U P (GLabel.under ρ :: es) (p ++ ρ.lhs ++ q) v
  | root {π : GDRule α} {es : List (GLabel α)} {v : List (GLetter α)} (q : List (GLetter α)) :
      π ∈ P → GDChain U P es (π.rhs ++ q) v → GDChain U P (GLabel.root π :: es) (π.lhs ++ q) v

/-- The value `V(w) := ([w](x*))₁` (in homogeneous coordinates; `x* = (0, −∞, …, −∞)`). -/
def gV {R : Type} [CommSemiring R] {d : ℕ} (hd : 0 < d) (J : GLetter α → AffFun R d)
    (w : List (GLetter α)) : R :=
  (hom (gevA J w) *ᵥ xs hd) (c0 hd)

/-- `gV` is the first component of the linear function `[w]` applied to `x* = (0, −∞, …, −∞)`. -/
theorem gV_eq_apply {R : Type} [CommSemiring R] {d : ℕ} (hd : 0 < d) (J : GLetter α → AffFun R d)
    (w : List (GLetter α)) :
    gV hd J w = (gevA J w).apply (fun j => if j = ⟨0, hd⟩ then 1 else 0) ⟨0, hd⟩ := by
  unfold gV
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, c0, hom_cc, hom_cl, xs,
    Fin.lastCases_castSucc, Fin.lastCases_last, AffFun.apply, Pi.add_apply]
  simp

/-! ## Forms with the counting of uses as a parameter -/

/-- The sum of the counts `cnt` at the points of the orbit segment `n, f n, …, f^[m-1] n`. -/
def usesG (f : ℕ → ℕ) (cnt : ℕ → ℕ) (n m : ℕ) : ℕ :=
  ((List.range m).map (fun i => cnt (f^[i] n))).sum

/-- The form of `Gen.AutoRuleG` with the counting function as a parameter: for every automaton whose value is finite and does not increase by more than the slope `κ`
in a step of `f` at a point of the domain, there is, for every `N`, an orbit segment starting at a point `≥ N` (all of whose points lie in the domain) on which the number of uses `usesG f cnt` (plus `κ * lenT n`) exceeds the value. -/
def AutoUseG (f : ℕ → ℕ) (dom : ℕ → Prop) (cnt : ℕ → ℕ) : Prop :=
  ∀ (D : ℕ) (u : Fin D → Arc) (A : Interp D) (c : Fin D → Arc) (κ : ℕ),
    (∀ n, 1 ≤ n → autoVal u A c n ≠ 0) →
    (∀ n, dom n → ∀ a b : ℕ, autoVal u A c n = Arc.fin a → autoVal u A c (f n) = Arc.fin b →
      b + κ * lenT n ≤ a + κ * lenT (f n)) →
    ∀ N : ℕ, ∃ n, N ≤ n ∧ ∃ m : ℕ,
      (∀ i < m, dom (f^[i] n)) ∧ autoVal u A c n < Arc.fin (κ * lenT n + usesG f cnt n m)

/-- The form of `Gen.HUseR` with the counting function as a parameter: with probability close to 1, the sum of `cnt` along the family orbit (`steps β` steps from `R β + 2^m t`) is
at least `c k` for every `t` (condition (c) of Lemma 5.6). -/
def HUseC (f : ℕ → ℕ) (R steps : List Bool → ℕ) (cnt : ℕ → ℕ) : Prop :=
  ∀ β₀ : List Bool, ∃ c : ℚ, 0 < c ∧ ∀ ε : ℚ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀,
    1 - ε ≤ Prσ β₀ k (fun β => ∀ t : ℕ, 2 ^ (parityOf β).length ≤ t →
      c * k ≤ (usesG f cnt (R β + 2 ^ (parityOf β).length * t) (steps β) : ℚ))

/-- `AutoRuleG` is `AutoUseG` for the count `cnt n := (cd n).count ρ` (definitionally). -/
theorem autoRuleG_iff_use (f : ℕ → ℕ) (dom : ℕ → Prop) (cd : ℕ → List Rule) (ρ : Rule) :
    AutoRuleG f dom cd ρ ↔ AutoUseG f dom (fun n => (cd n).count ρ) := Iff.rfl

/-- `HUseR` is `HUseC` for the count `cnt n := (cd n).count ρ` (definitionally). -/
theorem hUseR_iff_use (f : ℕ → ℕ) (R steps : List Bool → ℕ) (cd : ℕ → List Rule) (ρ : Rule) :
    HUseR f R steps cd ρ ↔ HUseC f R steps (fun n => (cd n).count ρ) := Iff.rfl

/-- `AutoUseG` is monotone in the counting function (if `cnt ≤ cnt'` at points of the domain). -/
theorem AutoUseG.mono {f : ℕ → ℕ} {dom : ℕ → Prop} {cnt cnt' : ℕ → ℕ}
    (hle : ∀ n, dom n → cnt n ≤ cnt' n) (h : AutoUseG f dom cnt) : AutoUseG f dom cnt' := by
  intro D u A c κ hfin hsl N
  obtain ⟨n, hn, m, horb, hlt⟩ := h D u A c κ hfin hsl N
  refine ⟨n, hn, m, horb, lt_of_lt_of_le hlt ?_⟩
  rw [Arc.fin_le_fin]
  have : usesG f cnt n m ≤ usesG f cnt' n m :=
    List.sum_le_sum (fun i hi => hle _ (horb i (List.mem_range.mp hi)))
  omega

/-- `AutoUseG` is monotone in the domain (from the form with a smaller domain to the form with a larger one). -/
theorem AutoUseG.dom_mono {f : ℕ → ℕ} {dom dom' : ℕ → Prop} {cnt : ℕ → ℕ}
    (hsub : ∀ n, dom' n → dom n) (h : AutoUseG f dom' cnt) : AutoUseG f dom cnt :=
  fun D u A c κ hfin hsl N => by
    obtain ⟨n, hn, m, horb, hlt⟩ := h D u A c κ hfin (fun n hn => hsl n (hsub n hn)) N
    exact ⟨n, hn, m, fun i hi => hsub _ (horb i hi), hlt⟩

end Collatz.Arctic.DPGen
