/-
Chains of dependency pairs and values (the parts of the proof of Theorem 3.3 on homogeneous coordinates and values, non-increase, and decrease under strict orientation; Lemma 5.2).

* `dp h ρ`: the dependency pair `h# x ⋯ → h# y ⋯` of a root rule `h x ⋯ → h y ⋯`. `DChain U P`: chains on the string after `h#`, consisting of
  steps of `U` below the root and steps of dependency pairs (rules of `P`) at the root.
* The value `Vw h w := ([h# w](x*))₁` (homogeneous coordinates, `x* = (0, −∞, …, −∞)`). Steps below the root do not increase the value, by `WeakA` and monotonicity
  (`Vw_under`); steps of dependency pairs at the root do not increase it, by the first-row comparison (`Vw_root_weak`); and a strictly oriented dependency pair
  decreases it by the arctic 1 (`Vw_root_strict`; the same argument as for Lemma 5.1). The estimate along a chain is `Vw_chain`.
* The value is the value of an automaton reading binary digits (`Vw_fwd_eq` for the system; `Vw_rev_eq` for the reversal, by transposition). The estimate along an orbit is `orbit_chain`.
-/
import CollatzProof.Arctic.DPAlg
import CollatzProof.Arctic.Main

namespace Collatz.Arctic

open Matrix

/-! ### Chains of dependency pairs and values -/

/-- Reverse both sides of a rule (the reversed system). -/
def Rule.rev (ρ : Rule) : Rule := ⟨ρ.lhs.reverse, ρ.rhs.reverse⟩

lemma Rule.rev_injective : Function.Injective Rule.rev := by
  intro a b h
  cases a; cases b
  simp only [Rule.rev, Rule.mk.injEq, List.reverse_inj] at h
  rw [h.1, h.2]

/-- The dependency pair `h# x ⋯ → h# y ⋯` of a root rule `h x ⋯ → h y ⋯` (the first letter is marked, the others are unmarked). -/
def dp (h : Letter) (ρ : Rule) : DRule :=
  ⟨DLetter.mark h :: ρ.lhs.tail.map DLetter.plain, DLetter.mark h :: ρ.rhs.tail.map DLetter.plain⟩

/-- Chains of dependency pairs on the string after `h#`: steps of `U` below the root (`under`) and steps of dependency pairs at the root (`root`,
replacing `ρ.lhs.tail`, the left-hand side of a rule `ρ` of `P` after its first letter, by `ρ.rhs.tail`). The label is the list of rules. -/
inductive DChain (U P : List Rule) : List Rule → Word → Word → Prop
  | nil (w : Word) : DChain U P [] w w
  | under {ρ : Rule} {rs : List Rule} {u w v : Word} :
      ρ ∈ U → Step ρ u w → DChain U P rs w v → DChain U P (ρ :: rs) u v
  | root {ρ : Rule} {rs : List Rule} (q : Word) {v : Word} :
      ρ ∈ P → DChain U P rs (ρ.rhs.tail ++ q) v → DChain U P (ρ :: rs) (ρ.lhs.tail ++ q) v

section Value

variable {R : Type} [CommSemiring R] {d : ℕ}

/-- The index of the first component in homogeneous coordinates. -/
def c0 (hd : 0 < d) : Fin (d + 1) := Fin.castSucc ⟨0, hd⟩

/-- `x* = (0, −∞, …, −∞)` in homogeneous coordinates (the last component is 0). -/
def xs (hd : 0 < d) : Fin (d + 1) → R :=
  Fin.lastCases (motive := fun _ => R) 1 (fun i => if i = ⟨0, hd⟩ then 1 else 0)

/-- The matrices of the unmarked letters in homogeneous coordinates. -/
def homL (J : DLetter → AffFun R d) (s : Letter) : Matrix (Fin (d + 1)) (Fin (d + 1)) R :=
  hom (J (DLetter.plain s))

/-- The value `V(w) := ([h# w](x*))₁` (in homogeneous coordinates). -/
def Vw (hd : 0 < d) (J : DLetter → AffFun R d) (h : Letter) (w : Word) : R :=
  ((hom (J (DLetter.mark h)) * evR (homL J) w) *ᵥ xs hd) (c0 hd)

lemma hom_evA_plain (J : DLetter → AffFun R d) (w : Word) :
    hom (evA J (w.map DLetter.plain)) = evR (homL J) w := by
  rw [hom_evA, List.map_map]
  rfl

lemma hom_evA_dp_lhs (J : DLetter → AffFun R d) (h : Letter) (ρ : Rule) :
    hom (evA J (dp h ρ).lhs) = hom (J (DLetter.mark h)) * evR (homL J) ρ.lhs.tail := by
  rw [← hom_evA_plain, dp, ← hom_comp]
  rfl

lemma hom_evA_dp_rhs (J : DLetter → AffFun R d) (h : Letter) (ρ : Rule) :
    hom (evA J (dp h ρ).rhs) = hom (J (DLetter.mark h)) * evR (homL J) ρ.rhs.tail := by
  rw [← hom_evA_plain, dp, ← hom_comp]
  rfl

/-- Splitting the value at a point of the string. -/
lemma Vw_split (hd : 0 < d) (J : DLetter → AffFun R d) (h : Letter) (w₁ q : Word) :
    Vw hd J h (w₁ ++ q) =
      ((hom (J (DLetter.mark h)) * evR (homL J) w₁) *ᵥ (evR (homL J) q *ᵥ xs hd)) (c0 hd) := by
  rw [Vw, evR_append, ← Matrix.mul_assoc, ← Matrix.mulVec_mulVec]

end Value

section ValueOrder

variable {R : Type} [CommSemiring R] [LinearOrder R] [ArcticOrder R] {d : ℕ}

/-- A step below the root by a weakly oriented rule does not increase the value. -/
lemma Vw_under (hd : 0 < d) (J : DLetter → AffFun R d) (h : Letter) {ρ : Rule}
    (hw : WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs)) (p q : Word) :
    Vw hd J h (p ++ ρ.rhs ++ q) ≤ Vw hd J h (p ++ ρ.lhs ++ q) := by
  have hle : ∀ i j, evR (homL J) ρ.rhs i j ≤ evR (homL J) ρ.lhs i j := by
    have := hom_le_of_weakA hw
    rwa [Rule.plain, hom_evA_plain, hom_evA_plain] at this
  unfold Vw
  rw [evR_append, evR_append, evR_append, evR_append]
  refine ao_mulVec_mono ?_ (fun _ => le_rfl) _
  refine ao_mul_mono (fun _ _ => le_rfl) ?_
  exact ao_mul_mono (ao_mul_mono (fun _ _ => le_rfl) hle) (fun _ _ => le_rfl)

/-- A weakly oriented step of a dependency pair at the root does not increase the value. -/
lemma Vw_root_weak (hd : 0 < d) (J : DLetter → AffFun R d) (h : Letter) {ρ : Rule}
    (hw : WeakTop hd (evA J (dp h ρ).lhs) (evA J (dp h ρ).rhs)) (q : Word) :
    Vw hd J h (ρ.rhs.tail ++ q) ≤ Vw hd J h (ρ.lhs.tail ++ q) := by
  have hle := hom_top_le_of_weakTop hd hw
  rw [hom_evA_dp_lhs, hom_evA_dp_rhs] at hle
  rw [Vw_split, Vw_split]
  simp only [Matrix.mulVec, dotProduct]
  exact ao_sum_mono _ (fun j _ => ArcticOrder.mul_mono (hle j) le_rfl)

/-- A strictly oriented step of a dependency pair at the root decreases the value by `e` (the arctic 1) (the same argument as for Lemma 5.1). -/
lemma Vw_root_strict (hd : 0 < d) (J : DLetter → AffFun R d) (h : Letter) (e : R)
    (he : ∀ l r : R, GG l r → r * e ≤ l) {ρ : Rule}
    (hs : StrictTop hd (evA J (dp h ρ).lhs) (evA J (dp h ρ).rhs)) (q : Word) :
    Vw hd J h (ρ.rhs.tail ++ q) * e ≤ Vw hd J h (ρ.lhs.tail ++ q) := by
  have hgg := hom_top_gg_of_strictTop hd hs
  rw [hom_evA_dp_lhs, hom_evA_dp_rhs] at hgg
  rw [Vw_split, Vw_split]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_mul]
  refine ao_sum_mono _ (fun j _ => ?_)
  rw [mul_right_comm]
  exact ArcticOrder.mul_mono (he _ _ (hgg j)) le_rfl

/-- The estimate along a chain of dependency pairs: the value decreases by `e` for each root step of a strictly oriented `σ ∈ P` (`σ ∉ U`). -/
theorem Vw_chain (hd : 0 < d) (J : DLetter → AffFun R d) (h : Letter) (e : R)
    (he : ∀ l r : R, GG l r → r * e ≤ l) {U P : List Rule}
    (hU : ∀ ρ ∈ U, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs))
    (hP : ∀ ρ ∈ P, WeakTop hd (evA J (dp h ρ).lhs) (evA J (dp h ρ).rhs))
    {σ : Rule} (hσU : σ ∉ U) (hσ : StrictTop hd (evA J (dp h σ).lhs) (evA J (dp h σ).rhs)) :
    ∀ {rs : List Rule} {u v : Word}, DChain U P rs u v →
      Vw hd J h v * e ^ (rs.count σ) ≤ Vw hd J h u := by
  intro rs u v hc
  induction hc with
  | nil w => simp
  | @under ρ rs u w v hρ hstep _ ih =>
    have hne : ρ ≠ σ := fun heq => hσU (heq ▸ hρ)
    rw [List.count_cons_of_ne hne]
    obtain ⟨p, q, rfl, rfl⟩ := hstep
    exact ih.trans (Vw_under hd J h (hU ρ hρ) p q)
  | @root ρ rs q v hρ _ ih =>
    by_cases hρσ : ρ = σ
    · subst hρσ
      rw [List.count_cons_self, pow_succ, ← mul_assoc]
      exact (ArcticOrder.mul_mono ih le_rfl).trans (Vw_root_strict hd J h e he hσ q)
    · rw [List.count_cons_of_ne hρσ]
      exact ih.trans (Vw_root_weak hd J h (hP ρ hρ) q)

end ValueOrder

section Orbit

variable {R : Type} [CommSemiring R] [LinearOrder R] [ArcticOrder R]

/-- The estimate along an orbit (accumulating the estimates for the steps of `T`). -/
lemma orbit_chain (V : ℕ → R) (e : R) (σ : Rule)
    (hstep : ∀ n, 2 ≤ n → V (T n) * e ^ (uses σ n) ≤ V n) :
    ∀ m n, (∀ i < m, 2 ≤ T^[i] n) → V (T^[m] n) * e ^ (usesOrbit σ n m) ≤ V n := by
  intro m
  induction m with
  | zero => intro n _; simp [usesOrbit_zero]
  | succ m ih =>
    intro n horb
    have hn : 2 ≤ n := by simpa using horb 0 (Nat.succ_pos m)
    have horb' : ∀ i < m, 2 ≤ T^[i] (T n) := by
      intro i hi
      have := horb (i + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    rw [Function.iterate_succ_apply, usesOrbit_succ, pow_add, mul_comm (e ^ _), ← mul_assoc]
    exact (ArcticOrder.mul_mono (ih (T n) horb') le_rfl).trans (hstep n hn)

end Orbit

section Fin

variable {R : Type} [CommSemiring R] {d : ℕ}

/-- The last (homogeneous) component of the value vector is 0 (the arctic 1). -/
lemma yvec_last (hd : 0 < d) (J : DLetter → AffFun R d) :
    ∀ w : Word, (evR (homL J) w *ᵥ xs hd) (Fin.last d) = 1 := by
  intro w
  induction w with
  | nil => simp [evR_nil, xs]
  | cons s w ih =>
    rw [evR_cons, ← Matrix.mulVec_mulVec, homL, hom_mulVec_last, ih]

/-- The value is the first component of the product of the matrix of `h#` in homogeneous coordinates with the value vector `[w](x*)`. -/
lemma Vw_eq_mulVec (hd : 0 < d) (J : DLetter → AffFun R d) (h : Letter) (w : Word) :
    Vw hd J h w = (hom (J (DLetter.mark h)) *ᵥ (evR (homL J) w *ᵥ xs hd)) (c0 hd) := by
  rw [Vw, Matrix.mulVec_mulVec]

end Fin

section FinOrder

variable {R : Type} [CommSemiring R] [LinearOrder R] [ArcticOrder R] {d : ℕ}

/-- The first component is at least `M[1,1] ⊗ y[1]`. -/
lemma hom_mulVec_ge_M (hd : 0 < d) (f : AffFun R d) (y : Fin (d + 1) → R) :
    f.M ⟨0, hd⟩ ⟨0, hd⟩ * y (c0 hd) ≤ (hom f *ᵥ y) (c0 hd) := by
  simp only [Matrix.mulVec, dotProduct]
  have := ao_le_sum (s := Finset.univ) (fun j => hom f (c0 hd) j * y j) (Finset.mem_univ (c0 hd))
  simpa only [c0, hom_cc] using this

/-- The first component is at least `c[1] ⊗ y[d+1]` (the absolute part, through the homogeneous component). -/
lemma hom_mulVec_ge_c (hd : 0 < d) (f : AffFun R d) (y : Fin (d + 1) → R) :
    f.c ⟨0, hd⟩ * y (Fin.last d) ≤ (hom f *ᵥ y) (c0 hd) := by
  simp only [Matrix.mulVec, dotProduct]
  have := ao_le_sum (s := Finset.univ) (fun j => hom f (c0 hd) j * y j)
    (Finset.mem_univ (Fin.last d))
  simpa only [c0, hom_cl] using this

end FinOrder

section Auto

variable {R : Type} [CommSemiring R] {d : ℕ}

/-- The value for the system is the value of an automaton reading the binary digits from the top. -/
lemma Vw_fwd_eq (hd : 0 < d) (J : DLetter → AffFun R d) (n : ℕ) :
    Vw hd J Letter.lft (binTail n ++ [Letter.rgt]) =
      (fun j => hom (J (DLetter.mark Letter.lft)) (c0 hd) j) ⬝ᵥ
        (evR (homL J) (binTail n) *ᵥ (homL J Letter.rgt *ᵥ xs hd)) := by
  rw [Vw_split, ← Matrix.mulVec_mulVec]
  simp only [evR, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rfl

/-- The value for the reversal is, after transposition, the value of an automaton reading the binary digits from the top. -/
lemma Vw_rev_eq (hd : 0 < d) (J : DLetter → AffFun R d) (n : ℕ) :
    Vw hd J Letter.rgt ((binTail n).reverse ++ [Letter.lft]) =
      (homL J Letter.lft *ᵥ xs hd) ⬝ᵥ
        (evR (fun s => (homL J s)ᵀ) (binTail n) *ᵥ
          (fun j => hom (J (DLetter.mark Letter.rgt)) (c0 hd) j)) := by
  rw [Vw_split, ← Matrix.mulVec_mulVec]
  simp only [evR, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  change (fun j => hom (J (DLetter.mark Letter.rgt)) (c0 hd) j) ⬝ᵥ
      (evR (homL J) (binTail n).reverse *ᵥ (homL J Letter.lft *ᵥ xs hd)) = _
  rw [Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose,
    evR_reverse_transpose]
  rfl

end Auto

end Collatz.Arctic
