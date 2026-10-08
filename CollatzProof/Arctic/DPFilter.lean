/-
Proofs of the arctic barrier for dependency pairs with argument filters (the remark on argument filters after Theorem 3.4 of the paper;
the statements are in `DPFilterStatement.lean`).

A finding of an internal independent review of the natural-number statements for dependency pairs: for the reversed problem the usable rules
`U_R(P, π)` of Giesl–Thiemann–Schneider-Kamp–Falke 2006, Definition 21, shrink under an argument filter `π` (Definition 11; regarded positions, Definition 20), which is outside the hypotheses of the frozen statements (`DPStatement.lean`, `HTPDB/DPStatement.lean`).
The natural-number case is in `Nat/BridgeDPFilter.lean`. This file treats the arctic case (`𝔸_ℕ` with somewhere finiteness, and below zero with absolute positivity).

* §1 Usable rules with a filter (a combinatorial computation that does not depend on the interpretation; for $\mathcal T$ we use `usableFilt_fwd` and
  `usableFilt_rev` of `Nat/BridgeDPFilter.lean` as they are):
  - Forward: for both $\mathcal T$ and $\mathcal H$, `U = D ∪ A` (8 rules) for every filter. Directly below `/#` stand `f` and `t`, and the rules of `f` and `t` form
    all of `U` (`usableFiltH_fwd`).
  - Reversed: for $\mathcal T^{\mathrm{rev}}$, 3 rules (`2f → f1`, `2t → t2`, `2/ → tf/`) if the argument of `f` is dropped, and 6 rules if that of `f` is regarded and that of `t` is dropped
    (the rules of `1` and `2`). For $\mathcal H^{\mathrm{rev}}$, 6 rules (the rules of `0` and `2`, `usableRevHFT`) if the arguments of both `f` and `t` are dropped. For the other
    filters, `A^rev ∪ B^rev` (`usableFiltH_rev`).
* §2 Lemmas over a general semiring: a symbol whose matrix is 0 (−∞) is a constant (`comp_const`), a value that starts with such a symbol does not depend on the rest
  (`Vw_head_const`), and if the first row of the marked symbol is 0, no dependency pair is strictly oriented in the first row (`not_strictTop_of_row0`).
* §3 Proofs for the shrinking cases (using neither `AutoCore` nor the value-level core; (a) uses only the weak orientation of the pair `.#f → .#`, (b) and (c) only a short chain and
  the equality of values caused by a constant symbol):
  - $\mathcal T^{\mathrm{rev}}$, the argument of `f` dropped: the weak orientation of `.#f → .#` in the first row makes the first row of `[.#]` equal to −∞. The first rows of both sides of the pairs are the same constant
    `c_{.#}[1]`, which is finite by somewhere finiteness (by absolute positivity for below zero), so no pair is strictly oriented.
  - $\mathcal T^{\mathrm{rev}}$, the argument of `t` dropped: along the chain `.#tff/ → .#2ff/ → .#f1f/ → .#1f/ → .#t0/` (which uses `2f → f1` and `1f → t0` of the 6 rules and
    each pair once) the value decreases by the strictly oriented pair. As `[t]` is constant, `V(tff/) = V(t0/)`, and as the value is finite, this is a contradiction.
  - $\mathcal H^{\mathrm{rev}}$, the arguments of `f` and `t` dropped: `.#fff/ → .#0f/ → .#f0/` and `.#tttt/ → .#22t/ → .#2t2/ → .#t22/`. The same argument.
* §4 The main theorems with filters (without hypotheses): for filters that do not shrink the usable rules, from the main theorems for the frozen statements (`Summary.lean`, `HTPDB/Final.lean`);
  for filters that shrink them, from §3. If the argument of the marked symbol is dropped: `markConst_not_strict_arc`, `_arcZ` (trivial).
* The four below-zero statements (`arcticBarrierBZFilt` etc.) require absolute positivity of all symbols, so they do not include collapsing filters (the identity)
  (internal independent review). The forms under the weaker hypothesis `BZPos`, which include collapsing filters, are in `DPFilterBZ.lean`.
-/
import CollatzProof.Arctic.DPFilterStatement
import CollatzProof.Arctic.Summary
import CollatzProof.Arctic.HTPDB.Final

namespace Collatz.Arctic.DPFilter

open Collatz.Arctic Matrix Letter DLetter
open Collatz.Arctic.NatQ5.W5 (usableFilt usableFilt_congr filter_mem_iff filter_mem_sublists lettersAll
  usableRevF usableRevT usableFilt_rev usableFilt_fwd filtIter regPrefix dpTail pairsPDrev_head pairsPB_head)

/-! ## §1 Usable rules of $\mathcal H$ with a filter (Giesl et al. 2006, Definition 21) -/

/-- The usable rules of $\mathcal H^{\mathrm{rev}}$ when the arguments of both `f` and `t` are dropped (6 rules: the rules of `0` and `2`). -/
def usableRevHFT : List Rule :=
  [⟨[d0, f], [f, d0]⟩, ⟨[d2, f], [f, d1]⟩, ⟨[d0, t], [t, d1]⟩, ⟨[d2, t], [t, d2]⟩,
    ⟨[d0, lft], [t, lft]⟩, ⟨[d2, lft], [t, f, lft]⟩]

theorem usableFiltH_rev_table : ∀ G ∈ lettersAll.sublists,
    usableFilt HTPDB.NonVacuityH.rulesHTrev HTPDB.pairsPDrevH G =
      if f ∈ G ∧ t ∈ G then usableRevHFT else HTPDB.usableHTrev := by
  decide +kernel

theorem usableFiltH_fwd_table : ∀ G ∈ lettersAll.sublists,
    usableFilt HTPDB.rulesHT pairsPB G = HTPDB.usableHT := by
  decide +kernel

/-- The closure is stable after 7 steps (for every filter the 8th step adds no new symbol; both directions of $\mathcal H$). -/
theorem filtIterH_stable : ∀ G ∈ lettersAll.sublists,
    (∀ x ∈ filtIter HTPDB.NonVacuityH.rulesHTrev (regPrefix G)
        (HTPDB.pairsPDrevH.flatMap fun π => regPrefix G (dpTail π)) 8,
      x ∈ filtIter HTPDB.NonVacuityH.rulesHTrev (regPrefix G)
        (HTPDB.pairsPDrevH.flatMap fun π => regPrefix G (dpTail π)) 7) ∧
    (∀ x ∈ filtIter HTPDB.rulesHT (regPrefix G) (pairsPB.flatMap fun π => regPrefix G (dpTail π)) 8,
      x ∈ filtIter HTPDB.rulesHT (regPrefix G) (pairsPB.flatMap fun π => regPrefix G (dpTail π)) 7) := by
  decide +kernel

/-- **The usable rules of $\mathcal H^{\mathrm{rev}}$ with a filter**: 6 rules if the arguments of both `f` and `t` are dropped, otherwise `A^rev ∪ B^rev`. -/
theorem usableFiltH_rev (F : List Letter) :
    usableFilt HTPDB.NonVacuityH.rulesHTrev HTPDB.pairsPDrevH F =
      if f ∈ F ∧ t ∈ F then usableRevHFT else HTPDB.usableHTrev := by
  rw [usableFilt_congr _ _ (filter_mem_iff F), usableFiltH_rev_table _ (filter_mem_sublists F)]
  simp only [← filter_mem_iff]

/-- **The forward usable rules of $\mathcal H$ with a filter**: `U = D_H ∪ A` for every filter. -/
theorem usableFiltH_fwd (F : List Letter) : usableFilt HTPDB.rulesHT pairsPB F = HTPDB.usableHT := by
  rw [usableFilt_congr _ _ (filter_mem_iff F), usableFiltH_fwd_table _ (filter_mem_sublists F)]

/-- Without a filter, the usable rules agree with the four frozen lists (the usable rules of Giesl et al. 2006, Definition 10). -/
theorem usableFilt_nil :
    usableFilt rulesST pairsPB [] = usableST ∧ usableFilt NatQ5.rulesSTrev pairsPDrev [] = usableSTrev ∧
      usableFilt HTPDB.rulesHT pairsPB [] = HTPDB.usableHT ∧
      usableFilt HTPDB.NonVacuityH.rulesHTrev HTPDB.pairsPDrevH [] = HTPDB.usableHTrev := by
  decide +kernel

/-- The shrunk usable rules are contained in the frozen lists (the 3 rules and the 6 rules of $\mathcal T^{\mathrm{rev}}$, the 6 rules of $\mathcal H^{\mathrm{rev}}$). -/
theorem usableRev_sub :
    (∀ ρ ∈ usableRevF, ρ ∈ usableSTrev) ∧ (∀ ρ ∈ usableRevT, ρ ∈ usableSTrev) ∧
      (∀ ρ ∈ usableRevHFT, ρ ∈ HTPDB.usableHTrev) := by
  decide

/-! ## §2 Lemmas over a general semiring -/

section Gen

variable {R : Type} [CommSemiring R] {d : ℕ}

/-- A linear function whose matrix is 0 (−∞), that is, a constant, does not change under composition with any function on the right. -/
theorem comp_const (F G : AffFun R d) (hF : F.M = 0) : F.comp G = F := by
  obtain ⟨M, c⟩ := F
  simp only at hF
  subst hF
  simp [AffFun.comp]

theorem evA_cons_const (J : DLetter → AffFun R d) {s : DLetter} (hs : (J s).M = 0) (w : List DLetter) :
    evA J (s :: w) = J s := by
  show (J s).comp (evA J w) = J s
  exact comp_const _ _ hs

/-- If the matrix of the leading unmarked symbol is 0, the value `V(s w) = ([h# s w](x*))₁` does not depend on the rest `w` of the string. -/
theorem Vw_head_const (hd : 0 < d) (J : DLetter → AffFun R d) (h s : Letter) (hs : (J (plain s)).M = 0)
    (w w' : Word) : Vw hd J h (s :: w) = Vw hd J h (s :: w') := by
  unfold Vw
  rw [← hom_evA_plain J (s :: w), ← hom_evA_plain J (s :: w'), List.map_cons, List.map_cons,
    evA_cons_const J hs, evA_cons_const J hs]

/-- If the first row of the matrix of `h#` is 0, then for a string that starts with `h#` the first row of the matrix of its interpretation is 0 and the first component of its absolute part is `c_{h#}[1]`. -/
theorem evA_mark_row0 (hd : 0 < d) (J : DLetter → AffFun R d) (h : Letter)
    (hrow : ∀ j, (J (mark h)).M ⟨0, hd⟩ j = 0) (w : List DLetter) :
    (∀ j, (evA J (mark h :: w)).M ⟨0, hd⟩ j = 0) ∧
      (evA J (mark h :: w)).c ⟨0, hd⟩ = (J (mark h)).c ⟨0, hd⟩ := by
  show (∀ j, ((J (mark h)).comp (evA J w)).M ⟨0, hd⟩ j = 0) ∧
    ((J (mark h)).comp (evA J w)).c ⟨0, hd⟩ = _
  simp [AffFun.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, hrow]

/-- If the first row of the matrix of `h#` is 0 and the first component of its absolute part is finite, no dependency pair that starts with `h#` is strictly oriented in the first row
(the first components of the absolute parts of both sides are the same finite value, and `≫` fails). -/
theorem not_strictTop_of_row0 [LinearOrder R] (hd : 0 < d) (J : DLetter → AffFun R d) (h : Letter)
    (hrow : ∀ j, (J (mark h)).M ⟨0, hd⟩ j = 0) (hc : (J (mark h)).c ⟨0, hd⟩ ≠ 0) (l r : List DLetter) :
    ¬ StrictTop hd (evA J (mark h :: l)) (evA J (mark h :: r)) := by
  rintro ⟨-, hs⟩
  rw [(evA_mark_row0 hd J h hrow l).2, (evA_mark_row0 hd J h hrow r).2] at hs
  rcases hs with hlt | ⟨h0, -⟩
  · exact lt_irrefl _ hlt
  · exact hc h0

/-- If `[s]` is constant (its matrix is 0) and the dependency pair `h# s → h#` is weakly oriented in the first row, then the first row of the matrix of `h#` is 0 (−∞). -/
theorem row0_zero_of_weakTop [LinearOrder R] [ArcticOrder R] (hd : 0 < d) (J : DLetter → AffFun R d)
    (h s : Letter) (hs : (J (plain s)).M = 0)
    (hw : WeakTop hd (evA J [mark h, plain s]) (evA J [mark h])) :
    ∀ j, (J (mark h)).M ⟨0, hd⟩ j = 0 := by
  intro j
  have h1 := hw.1 j
  have e1 : evA J [mark h, plain s] = (J (mark h)).comp (J (plain s)) := by
    show (J (mark h)).comp (evA J [plain s]) = _
    rw [evA_cons_const J hs]
  have e2 : (evA J [mark h]).M = (J (mark h)).M := by simp [evA, AffFun.comp, AffFun.id]
  rw [e1, e2] at h1
  simp only [AffFun.comp, hs, Matrix.mul_zero, Matrix.zero_apply] at h1
  refine le_antisymm h1 ?_
  have := ArcticOrder.le_add (0 : R) ((J (mark h)).M ⟨0, hd⟩ j)
  rwa [zero_add] at this

end Gen

/-! ## §3 Proofs for the shrinking cases -/

/-- A root step by a dependency pair (with the words given by equations). -/
theorem dchain_root {U P : List Rule} {ρ : Rule} {rs : List Rule} {u w v : Word} (q : Word) (hρ : ρ ∈ P)
    (hu : u = ρ.lhs.tail ++ q) (hw : w = ρ.rhs.tail ++ q) (hc : DChain U P rs w v) :
    DChain U P (ρ :: rs) u v := by
  subst hu hw
  exact DChain.root q hρ hc

/-- The root rule `.f → .` of $\mathcal T^{\mathrm{rev}}$ (`.#f → .#` by `dp rgt`). -/
def rootF : Rule := Rule.rev ⟨[f, rgt], [rgt]⟩

/-- The root rule `.t → .2` of $\mathcal T^{\mathrm{rev}}$ (`.#t → .#2` by `dp rgt`). -/
def rootT : Rule := Rule.rev ⟨[t, rgt], [d2, rgt]⟩

theorem rootPDrev_eq' : rootPDrev = [rootF, rootT] := rfl

/-- The chain for $\mathcal T^{\mathrm{rev}}$ when the argument of `t` is dropped: `.#tff/ → .#2ff/ → .#f1f/ → .#1f/ → .#t0/` (the root steps use each of the two pairs once,
the steps below the root use `2f → f1` and `1f → t0` of the 6 rules). -/
theorem chainST_t :
    DChain usableRevT rootPDrev [rootT, ⟨[d2, f], [f, d1]⟩, rootF, ⟨[d1, f], [t, d0]⟩]
      [t, f, f, lft] [t, d0, lft] := by
  refine dchain_root (w := [d2, f, f, lft]) [f, f, lft] (by decide) (by decide) (by decide) ?_
  refine DChain.under (w := [f, d1, f, lft]) (by decide) ⟨[], [f, lft], by decide, by decide⟩ ?_
  refine dchain_root (w := [d1, f, lft]) [d1, f, lft] (by decide) (by decide) (by decide) ?_
  exact DChain.under (by decide) ⟨[], [lft], by decide, by decide⟩ (DChain.nil _)

theorem chainST_t_count : ∀ σ ∈ rootPDrev,
    [rootT, (⟨[d2, f], [f, d1]⟩ : Rule), rootF, ⟨[d1, f], [t, d0]⟩].count σ = 1 ∧ σ ∉ usableRevT := by
  decide

/-- A chain of $\mathcal H^{\mathrm{rev}}$ (`.#fff/ → .#0f/ → .#f0/`). -/
theorem chainH_ff :
    DChain usableRevHFT HTPDB.rootPDrevH [Rule.rev HTPDB.ffRule, ⟨[d0, f], [f, d0]⟩]
      [f, f, f, lft] [f, d0, lft] := by
  refine dchain_root (w := [d0, f, lft]) [f, lft] (by decide) (by decide) (by decide) ?_
  exact DChain.under (by decide) ⟨[], [lft], by decide, by decide⟩ (DChain.nil _)

/-- A chain of $\mathcal H^{\mathrm{rev}}$ (`.#tttt/ → .#22t/ → .#2t2/ → .#t22/`). -/
theorem chainH_ttt :
    DChain usableRevHFT HTPDB.rootPDrevH
      [Rule.rev HTPDB.tttRule, ⟨[d2, t], [t, d2]⟩, ⟨[d2, t], [t, d2]⟩]
      [t, t, t, t, lft] [t, d2, d2, lft] := by
  refine dchain_root (w := [d2, d2, t, lft]) [t, lft] (by decide) (by decide) (by decide) ?_
  refine DChain.under (w := [d2, t, d2, lft]) (by decide) ⟨[d2], [lft], by decide, by decide⟩ ?_
  exact DChain.under (by decide) ⟨[], [d2, lft], by decide, by decide⟩ (DChain.nil _)

theorem chainH_count :
    [Rule.rev HTPDB.ffRule, (⟨[d0, f], [f, d0]⟩ : Rule)].count (Rule.rev HTPDB.ffRule) = 1 ∧
      [Rule.rev HTPDB.tttRule, (⟨[d2, t], [t, d2]⟩ : Rule), ⟨[d2, t], [t, d2]⟩].count
        (Rule.rev HTPDB.tttRule) = 1 ∧
      Rule.rev HTPDB.ffRule ∉ usableRevHFT ∧ Rule.rev HTPDB.tttRule ∉ usableRevHFT := by
  decide

section Core

variable {R : Type} [CommSemiring R] [LinearOrder R] [ArcticOrder R] {d : ℕ}

/-- **The value estimate for $\mathcal T^{\mathrm{rev}}$ when the argument of `t` is dropped** (general semiring): if `[t]` is constant, the 6 rules are weakly oriented coefficientwise, the pairs of `P_D^rev` weakly in the first row,
and one of them strictly, then `V(tff/) ⊗ e ≤ V(tff/)`. -/
theorem rev_t_value (hd : 0 < d) (J : DLetter → AffFun R d) (e : R) (he : ∀ l r : R, GG l r → r * e ≤ l)
    (ht : (J (plain t)).M = 0) (hU : ∀ ρ ∈ usableRevT, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs))
    (hP : ∀ π ∈ pairsPDrev, WeakTop hd (evA J π.lhs) (evA J π.rhs))
    {π : DRule} (hπ : π ∈ pairsPDrev) (hs : StrictTop hd (evA J π.lhs) (evA J π.rhs)) :
    Vw hd J rgt [t, f, f, lft] * e ≤ Vw hd J rgt [t, f, f, lft] := by
  rw [pairsPDrev_eq] at hπ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hπ
  have hPw : ∀ ρ ∈ rootPDrev, WeakTop hd (evA J (dp rgt ρ).lhs) (evA J (dp rgt ρ).rhs) :=
    fun ρ hρ => hP _ (by rw [pairsPDrev_eq]; exact List.mem_map_of_mem hρ)
  obtain ⟨hcnt, hσU⟩ := chainST_t_count σ hσ
  have := Vw_chain hd J rgt e he hU hPw hσU hs chainST_t
  rwa [hcnt, pow_one, Vw_head_const hd J rgt t ht [d0, lft] [f, f, lft]] at this

/-- **The value estimate for $\mathcal H^{\mathrm{rev}}$ when the arguments of `f` and `t` are dropped** (general semiring). -/
theorem revH_ft_value (hd : 0 < d) (J : DLetter → AffFun R d) (e : R) (he : ∀ l r : R, GG l r → r * e ≤ l)
    (hf : (J (plain f)).M = 0) (ht : (J (plain t)).M = 0)
    (hU : ∀ ρ ∈ usableRevHFT, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs))
    (hP : ∀ π ∈ HTPDB.pairsPDrevH, WeakTop hd (evA J π.lhs) (evA J π.rhs))
    {π : DRule} (hπ : π ∈ HTPDB.pairsPDrevH) (hs : StrictTop hd (evA J π.lhs) (evA J π.rhs)) :
    Vw hd J rgt [f, f, f, lft] * e ≤ Vw hd J rgt [f, f, f, lft] ∨
      Vw hd J rgt [t, t, t, t, lft] * e ≤ Vw hd J rgt [t, t, t, t, lft] := by
  rw [HTPDB.pairsPDrevH_eq] at hπ
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hπ
  have hPw : ∀ ρ ∈ HTPDB.rootPDrevH, WeakTop hd (evA J (dp rgt ρ).lhs) (evA J (dp rgt ρ).rhs) :=
    fun ρ hρ => hP _ (by rw [HTPDB.pairsPDrevH_eq]; exact List.mem_map_of_mem hρ)
  obtain ⟨hc1, hc2, hn1, hn2⟩ := chainH_count
  simp only [HTPDB.rootPDrevH, List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl
  · left
    have := Vw_chain hd J rgt e he hU hPw hn1 hs chainH_ff
    rwa [hc1, pow_one, Vw_head_const hd J rgt f hf [d0, lft] [f, f, lft]] at this
  · right
    have := Vw_chain hd J rgt e he hU hPw hn2 hs chainH_ttt
    rwa [hc2, pow_one, Vw_head_const hd J rgt t ht [d2, d2, lft] [t, t, t, lft]] at this

end Core

/-! ### `𝔸_ℕ` (somewhere finite) -/

section ArcN

variable {d : ℕ}

theorem arc_not_succ_le {x : Arc} (hx : x ≠ 0) : ¬ x * Arc.fin 1 ≤ x := by
  obtain ⟨a, rfl⟩ := Arc.exists_fin_of_ne_zero hx
  rw [Arc.fin_mul_fin, Arc.fin_le_fin]
  omega

/-- **$\mathcal T^{\mathrm{rev}}$, the argument of `f` dropped (`𝔸_ℕ`)**: the weak orientation of `.#f → .#` in the first row alone implies that no dependency pair is strictly
oriented in the first row (no hypothesis on the usable rules is needed). -/
theorem dprev_filt_f_arc (hd : 0 < d) (J : DLetter → AffFun Arc d) (hSF : SomewhereFinite hd J lettersPDrev)
    (hf : (J (plain f)).M = 0) (hP0 : WeakTop hd (evA J [mark rgt, plain f]) (evA J [mark rgt])) :
    ∀ π ∈ pairsPDrev, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs) := by
  have hrow := row0_zero_of_weakTop hd J rgt f hf hP0
  have hc : (J (mark rgt)).c ⟨0, hd⟩ ≠ 0 := by
    rcases hSF (mark rgt) (by decide) with hc | hM
    · exact hc
    · exact absurd (hrow _) hM
  intro π hπ
  obtain ⟨l, r, hl, hr⟩ := pairsPDrev_head π hπ
  rw [hl, hr]
  exact not_strictTop_of_row0 hd J rgt hrow hc l r

/-- **$\mathcal T^{\mathrm{rev}}$, the argument of `t` dropped (`𝔸_ℕ`)**: although the usable rules shrink to 6 rules, no dependency pair is strictly oriented in the first row. -/
theorem dprev_filt_t_arc (hd : 0 < d) (J : DLetter → AffFun Arc d) (hSF : SomewhereFinite hd J lettersPDrev)
    (ht : (J (plain t)).M = 0) (hU : ∀ ρ ∈ usableRevT, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs))
    (hP : ∀ π ∈ pairsPDrev, WeakTop hd (evA J π.lhs) (evA J π.rhs)) :
    ∀ π ∈ pairsPDrev, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs) := fun _ hπ hs =>
  arc_not_succ_le (Vw_ne_zero hd J lettersPDrev hSF rgt (by decide) [t, f, f, lft] (by decide))
    (rev_t_value hd J (Arc.fin 1) (fun _ _ h => Arc.gg_mul_fin_one h) ht hU hP hπ hs)

/-- **$\mathcal H^{\mathrm{rev}}$, the arguments of `f` and `t` dropped (`𝔸_ℕ`)**. -/
theorem dprevH_filt_ft_arc (hd : 0 < d) (J : DLetter → AffFun Arc d) (hSF : SomewhereFinite hd J lettersPDrev)
    (hf : (J (plain f)).M = 0) (ht : (J (plain t)).M = 0)
    (hU : ∀ ρ ∈ usableRevHFT, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs))
    (hP : ∀ π ∈ HTPDB.pairsPDrevH, WeakTop hd (evA J π.lhs) (evA J π.rhs)) :
    ∀ π ∈ HTPDB.pairsPDrevH, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs) := by
  intro π hπ hs
  rcases revH_ft_value hd J (Arc.fin 1) (fun _ _ h => Arc.gg_mul_fin_one h) hf ht hU hP hπ hs with h1 | h2
  · exact arc_not_succ_le (Vw_ne_zero hd J lettersPDrev hSF rgt (by decide) [f, f, f, lft] (by decide)) h1
  · exact arc_not_succ_le (Vw_ne_zero hd J lettersPDrev hSF rgt (by decide) [t, t, t, t, lft] (by decide)) h2

end ArcN

/-! ### below zero `𝔸_ℤ` (absolutely positive) -/

section ArcZ

variable {d : ℕ}

theorem arcZ_ne_zero_of_pos {a : ArcZ} (h : ArcZ.fin 0 ≤ a) : a ≠ 0 := by
  obtain ⟨z, rfl⟩ := ArcZ.exists_nat_of_le h
  exact ArcZ.fin_ne_zero _

theorem arcZ_not_succ_le {x : ArcZ} (hx : x ≠ 0) : ¬ x * ArcZ.fin 1 ≤ x := by
  obtain ⟨a, rfl⟩ := ArcZ.exists_fin_of_ne_zero hx
  rw [ArcZ.fin_mul_fin, ArcZ.fin_le_fin]
  omega

/-- The values are finite (by absolute positivity `V ≥ c_{h#}[1] ≥ 0`; Koprowski–Waldmann 2009, Lemma 8.2). -/
theorem Vw_ne_zero_Z (hd : 0 < d) (J : DLetter → AffFun ArcZ d) (h : Letter)
    (hpos : ArcZ.fin 0 ≤ (J (mark h)).c ⟨0, hd⟩) (w : Word) : Vw hd J h w ≠ 0 := by
  obtain ⟨z, hz⟩ := Vw_nat hd J h hpos w
  rw [hz]
  exact ArcZ.fin_ne_zero _

/-- **$\mathcal T^{\mathrm{rev}}$, the argument of `f` dropped (below zero)**. -/
theorem dprev_filt_f_arcZ (hd : 0 < d) (J : DLetter → AffFun ArcZ d) (hAP : AbsPositive hd J lettersPDrev)
    (hf : (J (plain f)).M = 0) (hP0 : WeakTop hd (evA J [mark rgt, plain f]) (evA J [mark rgt])) :
    ∀ π ∈ pairsPDrev, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs) := by
  have hrow := row0_zero_of_weakTop hd J rgt f hf hP0
  have hc := arcZ_ne_zero_of_pos (hAP (mark rgt) (by decide))
  intro π hπ
  obtain ⟨l, r, hl, hr⟩ := pairsPDrev_head π hπ
  rw [hl, hr]
  exact not_strictTop_of_row0 hd J rgt hrow hc l r

/-- **$\mathcal T^{\mathrm{rev}}$, the argument of `t` dropped (below zero)**. -/
theorem dprev_filt_t_arcZ (hd : 0 < d) (J : DLetter → AffFun ArcZ d) (hAP : AbsPositive hd J lettersPDrev)
    (ht : (J (plain t)).M = 0) (hU : ∀ ρ ∈ usableRevT, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs))
    (hP : ∀ π ∈ pairsPDrev, WeakTop hd (evA J π.lhs) (evA J π.rhs)) :
    ∀ π ∈ pairsPDrev, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs) := fun _ hπ hs =>
  arcZ_not_succ_le (Vw_ne_zero_Z hd J rgt (hAP _ (by decide)) [t, f, f, lft])
    (rev_t_value hd J (ArcZ.fin 1) (fun _ _ h => ArcZ.gg_mul_fin_one h) ht hU hP hπ hs)

/-- **$\mathcal H^{\mathrm{rev}}$, the arguments of `f` and `t` dropped (below zero)**. -/
theorem dprevH_filt_ft_arcZ (hd : 0 < d) (J : DLetter → AffFun ArcZ d) (hAP : AbsPositive hd J lettersPDrev)
    (hf : (J (plain f)).M = 0) (ht : (J (plain t)).M = 0)
    (hU : ∀ ρ ∈ usableRevHFT, WeakA (evA J ρ.plain.lhs) (evA J ρ.plain.rhs))
    (hP : ∀ π ∈ HTPDB.pairsPDrevH, WeakTop hd (evA J π.lhs) (evA J π.rhs)) :
    ∀ π ∈ HTPDB.pairsPDrevH, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs) := by
  intro π hπ hs
  rcases revH_ft_value hd J (ArcZ.fin 1) (fun _ _ h => ArcZ.gg_mul_fin_one h) hf ht hU hP hπ hs with h1 | h2
  · exact arcZ_not_succ_le (Vw_ne_zero_Z hd J rgt (hAP _ (by decide)) [f, f, f, lft]) h1
  · exact arcZ_not_succ_le (Vw_ne_zero_Z hd J rgt (hAP _ (by decide)) [t, t, t, t, lft]) h2

end ArcZ

/-! ### The argument of the marked symbol dropped (trivial) -/

theorem pairsPDrevH_head : ∀ π ∈ HTPDB.pairsPDrevH, ∃ l r, π.lhs = mark rgt :: l ∧ π.rhs = mark rgt :: r := by
  intro π hπ
  simp only [HTPDB.pairsPDrevH, List.mem_cons, List.mem_nil_iff, or_false] at hπ
  rcases hπ with rfl | rfl <;> exact ⟨_, _, rfl, rfl⟩

/-- If the argument of the marked symbol `h#` is dropped (`M_{h#} = −∞`), no dependency pair that starts with `h#` is strictly oriented in the first row
(only somewhere finiteness or absolute positivity of `h#` is used; the usable rules are empty, and no hypothesis on them is needed). -/
theorem markConst_not_strict {R : Type} [CommSemiring R] [LinearOrder R] {d : ℕ} (hd : 0 < d)
    (J : DLetter → AffFun R d) (h : Letter) (hM : (J (mark h)).M = 0) (hc : (J (mark h)).c ⟨0, hd⟩ ≠ 0)
    (P : List DRule) (hP : ∀ π ∈ P, ∃ l r, π.lhs = mark h :: l ∧ π.rhs = mark h :: r) :
    ∀ π ∈ P, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs) := by
  intro π hπ
  obtain ⟨l, r, hl, hr⟩ := hP π hπ
  rw [hl, hr]
  exact not_strictTop_of_row0 hd J h (fun j => by simp [hM]) hc l r

/-- `𝔸_ℕ`: the three problems with the argument of the marked symbol dropped (`P_B`, `P_D^rev`, and `P_D^rev` of $\mathcal H$). -/
theorem markConst_not_strict_arc {d : ℕ} (hd : 0 < d) (J : DLetter → AffFun Arc d) :
    (SomewhereFinite hd J lettersPB → (J (mark lft)).M = 0 →
      ∀ π ∈ pairsPB, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)) ∧
    (SomewhereFinite hd J lettersPDrev → (J (mark rgt)).M = 0 →
      ∀ π ∈ pairsPDrev, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)) ∧
    (SomewhereFinite hd J lettersPDrev → (J (mark rgt)).M = 0 →
      ∀ π ∈ HTPDB.pairsPDrevH, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)) := by
  have key : ∀ (h : Letter) (S : List DLetter), mark h ∈ S → SomewhereFinite hd J S →
      (J (mark h)).M = 0 → (J (mark h)).c ⟨0, hd⟩ ≠ 0 := by
    intro h S hS hSF hM
    rcases hSF _ hS with hc | hM'
    · exact hc
    · exact absurd (by simp [hM]) hM'
  refine ⟨fun hSF hM => ?_, fun hSF hM => ?_, fun hSF hM => ?_⟩
  · exact markConst_not_strict hd J lft hM (key _ _ (by decide) hSF hM) _ pairsPB_head
  · exact markConst_not_strict hd J rgt hM (key _ _ (by decide) hSF hM) _ pairsPDrev_head
  · exact markConst_not_strict hd J rgt hM (key _ _ (by decide) hSF hM) _ pairsPDrevH_head

/-- below zero: the same three problems. -/
theorem markConst_not_strict_arcZ {d : ℕ} (hd : 0 < d) (J : DLetter → AffFun ArcZ d) :
    (AbsPositive hd J lettersPB → (J (mark lft)).M = 0 →
      ∀ π ∈ pairsPB, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)) ∧
    (AbsPositive hd J lettersPDrev → (J (mark rgt)).M = 0 →
      ∀ π ∈ pairsPDrev, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)) ∧
    (AbsPositive hd J lettersPDrev → (J (mark rgt)).M = 0 →
      ∀ π ∈ HTPDB.pairsPDrevH, ¬ StrictTop hd (evA J π.lhs) (evA J π.rhs)) := by
  refine ⟨fun hAP hM => ?_, fun hAP hM => ?_, fun hAP hM => ?_⟩
  · exact markConst_not_strict hd J lft hM (arcZ_ne_zero_of_pos (hAP _ (by decide))) _ pairsPB_head
  · exact markConst_not_strict hd J rgt hM (arcZ_ne_zero_of_pos (hAP _ (by decide))) _ pairsPDrev_head
  · exact markConst_not_strict hd J rgt hM (arcZ_ne_zero_of_pos (hAP _ (by decide))) _ pairsPDrevH_head

/-! ## §4 The main theorems with filters (without hypotheses) -/

/-- **Theorem 3.3 with an argument filter ($\mathcal T$, forward, `𝔸_ℕ`)**: the usable rules do not shrink under filters, so this follows from the frozen statement. -/
theorem arcticBarrierDPFilt : ArcticBarrierDPFilt := by
  intro F d hd J hSF _ hU hP
  rw [usableFilt_fwd] at hU
  exact arcticBarrierDP d hd J hSF hU hP

/-- **Theorem 3.3 with an argument filter ($\mathcal T$, reversed, `𝔸_ℕ`)**: if the argument of `f` or of `t` is dropped, by §3; otherwise from the frozen statement. -/
theorem arcticBarrierDPrevFilt : ArcticBarrierDPrevFilt := by
  intro F d hd J hSF hF hU hP
  rw [usableFilt_rev] at hU
  by_cases hf : f ∈ F
  · exact dprev_filt_f_arc hd J hSF (hF f hf) (hP ⟨[mark rgt, plain f], [mark rgt]⟩ (by decide))
  · by_cases ht : t ∈ F
    · simp only [hf, ht, ↓reduceIte] at hU
      exact dprev_filt_t_arc hd J hSF (hF t ht) hU hP
    · simp only [hf, ht, ↓reduceIte] at hU
      exact arcticBarrierDPrev d hd J hSF hU hP

/-- **Theorem 3.4 with an argument filter ($\mathcal T$, forward, below zero)**. -/
theorem arcticBarrierBZFilt : ArcticBarrierBZFilt := by
  intro F d hd J hAP _ hU hP
  rw [usableFilt_fwd] at hU
  exact arcticBarrierBZ d hd J hAP hU hP

/-- **Theorem 3.4 with an argument filter ($\mathcal T$, reversed, below zero)**. -/
theorem arcticBarrierBZrevFilt : ArcticBarrierBZrevFilt := by
  intro F d hd J hAP hF hU hP
  rw [usableFilt_rev] at hU
  by_cases hf : f ∈ F
  · exact dprev_filt_f_arcZ hd J hAP (hF f hf) (hP ⟨[mark rgt, plain f], [mark rgt]⟩ (by decide))
  · by_cases ht : t ∈ F
    · simp only [hf, ht, ↓reduceIte] at hU
      exact dprev_filt_t_arcZ hd J hAP (hF t ht) hU hP
    · simp only [hf, ht, ↓reduceIte] at hU
      exact arcticBarrierBZrev d hd J hAP hU hP

/-- **Theorem 3.3 with an argument filter ($\mathcal H$, forward, `𝔸_ℕ`)**. -/
theorem arcticBarrierHDPFilt : ArcticBarrierHDPFilt := by
  intro F d hd J hSF _ hU hP
  rw [usableFiltH_fwd] at hU
  exact HTPDB.arcticBarrierHDP d hd J hSF hU hP

/-- **Theorem 3.3 with an argument filter ($\mathcal H$, reversed, `𝔸_ℕ`)**. -/
theorem arcticBarrierHDPrevFilt : ArcticBarrierHDPrevFilt := by
  intro F d hd J hSF hF hU hP
  rw [usableFiltH_rev] at hU
  by_cases hft : f ∈ F ∧ t ∈ F
  · simp only [hft.1, hft.2, and_self, ↓reduceIte] at hU
    exact dprevH_filt_ft_arc hd J hSF (hF f hft.1) (hF t hft.2) hU hP
  · simp only [hft, ↓reduceIte] at hU
    exact HTPDB.arcticBarrierHDPrev d hd J hSF hU hP

/-- **Theorem 3.4 with an argument filter ($\mathcal H$, forward, below zero)**. -/
theorem arcticBarrierHBZFilt : ArcticBarrierHBZFilt := by
  intro F d hd J hAP _ hU hP
  rw [usableFiltH_fwd] at hU
  exact HTPDB.arcticBarrierHBZ d hd J hAP hU hP

/-- **Theorem 3.4 with an argument filter ($\mathcal H$, reversed, below zero)**. -/
theorem arcticBarrierHBZrevFilt : ArcticBarrierHBZrevFilt := by
  intro F d hd J hAP hF hU hP
  rw [usableFiltH_rev] at hU
  by_cases hft : f ∈ F ∧ t ∈ F
  · simp only [hft.1, hft.2, and_self, ↓reduceIte] at hU
    exact dprevH_filt_ft_arcZ hd J hAP (hF f hft.1) (hF t hft.2) hU hP
  · simp only [hft, ↓reduceIte] at hU
    exact HTPDB.arcticBarrierHBZrev d hd J hAP hU hP

/-- The eight statements with filters (without hypotheses). -/
theorem arcticBarrierFilt_all :
    ArcticBarrierDPFilt ∧ ArcticBarrierDPrevFilt ∧ ArcticBarrierBZFilt ∧ ArcticBarrierBZrevFilt ∧
      ArcticBarrierHDPFilt ∧ ArcticBarrierHDPrevFilt ∧ ArcticBarrierHBZFilt ∧ ArcticBarrierHBZrevFilt :=
  ⟨arcticBarrierDPFilt, arcticBarrierDPrevFilt, arcticBarrierBZFilt, arcticBarrierBZrevFilt,
    arcticBarrierHDPFilt, arcticBarrierHDPrevFilt, arcticBarrierHBZFilt, arcticBarrierHBZrevFilt⟩

end Collatz.Arctic.DPFilter
