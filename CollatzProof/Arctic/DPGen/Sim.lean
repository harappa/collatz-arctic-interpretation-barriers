/-
Lean foundation of Section 8 (Section 8.1): the general form of Lemma 5.6 (the simulation lemma).

For a dependency pair problem `(P, U)` over the symbol type `α`, an encoding `E : ℕ → List (GLetter α)` of integers by strings, a map `f`, a domain
`dom` and a counting function `cnt` for uses, the following three conditions imply that no arctic interpretation (of any dimension) that weakly orients `U` coefficientwise and `P` in the first row
strictly orients the pair `π` in the first row (`simulation_arc`, `simulation_arcZ`).
* (a) Rewrite sequences: for every point `n` of the domain there is a chain `GDChain U P` from `E n` to `E (f n)` in which `π` is used at the root
  at least `cnt n` times.
* (b) Finite-state values: the value `gV hd J (E n)` for the interpretation `J` equals the value `autoVal u A c n` of an automaton that reads the binary digits of `n`
  from the most significant digit (below zero, `autoValZ` with entries in `ℤ ∪ {−∞}`). An automaton reading from the least significant digit is converted by transposition
  (the reversed examples in `STCheck.lean`).
* (c) Uses: `AutoUseG f dom cnt` (the form of `Gen.AutoRuleG` with the counting function as a parameter; used with `κ = 0`, and with `κ = K` for the translation).
Over `𝔸_ℕ` the finiteness of the values is assumed instead of somewhere finiteness (it follows from somewhere finiteness by `Value.gV_ne_zero`);
below zero it is assumed that the values are bounded below (by 0 if absolutely positive, by `Value.gV_ge_head`).

The proof is that of Theorem 3.3: along the chain the value decreases by the number of uses of `π` (`Value.gV_chain`), and to the automaton of values
we apply `barrier_of_auto_arcG` (`𝔸_ℕ`) and `barrier_of_auto_arcZG` (translation, Lemma 5.3) of `Gen/SysBridge`.

**Family form** (`simulation_family_arc`, `simulation_family_arcZ`): (c) is obtained by Corollary 8.1 (`Family.autoUseG_family`)
from the window frequencies `HTerrasWinR M.R` and the numbers of uses `HUseC` along family orbits (condition (c) of Lemma 5.6 in the paper: with probability → 1, at least
`c_π k` uses for every `t`). Condition (a) is needed **only at points of family orbits** (as in Lemma 5.6 of the paper, at every family point).
-/
import CollatzProof.Arctic.DPGen.Value
import CollatzProof.Arctic.DPGen.Family
import CollatzProof.Arctic.Gen.SysBridge
import CollatzProof.Arctic.HSPMain

namespace Collatz.Arctic.DPGen

open Collatz.Arctic Collatz.Arctic.Gen Matrix

variable {α : Type} [DecidableEq α]

/-! ## `𝔸_ℕ` -/

/-- **Lemma 5.6 (`𝔸_ℕ`)**: from (a) chains at points of the domain with enough root uses of `π`, (b) values that are those of an automaton reading binary digits and are finite,
and (c) `AutoUseG`: an interpretation that weakly orients `U` coefficientwise and `P` in the first row does not strictly orient `π` in the first row. -/
theorem simulation_arc {f : ℕ → ℕ} {dom : ℕ → Prop} {cnt : ℕ → ℕ}
    (E : ℕ → List (GLetter α)) (U P : List (GDRule α)) (π : GDRule α)
    (ha : ∀ n, dom n → ∃ es, GDChain U P es (E n) (E (f n)) ∧ cnt n ≤ es.count (GLabel.root π))
    (hc : AutoUseG f dom cnt)
    {d : ℕ} (hd : 0 < d) (J : GLetter α → AffFun Arc d)
    (hb : ∃ (D : ℕ) (u : Fin D → Arc) (A : Interp D) (c : Fin D → Arc),
      ∀ n, gV hd J (E n) = autoVal u A c n)
    (hfin : ∀ n, gV hd J (E n) ≠ 0)
    (hU : ∀ ρ ∈ U, WeakA (gevA J ρ.lhs) (gevA J ρ.rhs))
    (hP : ∀ π' ∈ P, WeakTop hd (gevA J π'.lhs) (gevA J π'.rhs)) :
    ¬ StrictTop hd (gevA J π.lhs) (gevA J π.rhs) := by
  intro hs
  obtain ⟨D, u, A, c, hval⟩ := hb
  refine barrier_of_auto_arcG (autoCoreG_of_use hc) u A c σ₀ (List.mem_singleton_self _) ?_ ?_
  · intro n
    rw [← hval]
    exact hfin n
  · intro n hn
    rw [count_cdOf, ← hval, ← hval]
    obtain ⟨es, hch, hle⟩ := ha n hn
    have h1 := gV_chain hd J (Arc.fin 1) (fun _ _ h => Arc.gg_mul_fin_one h) hU hP hs hch
    refine le_trans (ArcticOrder.mul_mono le_rfl ?_) h1
    rw [Arc.fin_one_pow, Arc.fin_one_pow, Arc.fin_le_fin]
    exact hle

/-- Lemma 5.6 (`𝔸_ℕ`) with the chain labels given by a function `es` (`cnt n := (es n).count (root π)`). -/
theorem simulation_arc_es {f : ℕ → ℕ} {dom : ℕ → Prop}
    (E : ℕ → List (GLetter α)) (U P : List (GDRule α)) (π : GDRule α) (es : ℕ → List (GLabel α))
    (ha : ∀ n, dom n → GDChain U P (es n) (E n) (E (f n)))
    (hc : AutoUseG f dom (fun n => (es n).count (GLabel.root π)))
    {d : ℕ} (hd : 0 < d) (J : GLetter α → AffFun Arc d)
    (hb : ∃ (D : ℕ) (u : Fin D → Arc) (A : Interp D) (c : Fin D → Arc),
      ∀ n, gV hd J (E n) = autoVal u A c n)
    (hfin : ∀ n, gV hd J (E n) ≠ 0)
    (hU : ∀ ρ ∈ U, WeakA (gevA J ρ.lhs) (gevA J ρ.rhs))
    (hP : ∀ π' ∈ P, WeakTop hd (gevA J π'.lhs) (gevA J π'.rhs)) :
    ¬ StrictTop hd (gevA J π.lhs) (gevA J π.rhs) :=
  simulation_arc E U P π (fun n hn => ⟨es n, ha n hn, le_rfl⟩) hc hd J hb hfin hU hP

/-! ## Below zero (`𝔸_ℤ`) -/

/-- Multiplying the initial vector of the automaton uniformly by `a` multiplies the value by `a`. -/
theorem autoValZ_smul {D : ℕ} (a : ArcZ) (u : Fin D → ArcZ)
    (A : Letter → Matrix (Fin D) (Fin D) ArcZ) (c : Fin D → ArcZ) (n : ℕ) :
    autoValZ (a • u) A c n = a * autoValZ u A c n := by
  simp [autoValZ, smul_dotProduct]

/-- **Lemma 5.6 (below zero)**: instead of the finiteness of the values in the `𝔸_ℕ` form, assume that the values are bounded below (by `B`).
Translate the initial vector by `−B` to make the values natural numbers, and apply `barrier_of_auto_arcZG` (Lemma 5.3). -/
theorem simulation_arcZ {f : ℕ → ℕ} {dom : ℕ → Prop} {cnt : ℕ → ℕ}
    (E : ℕ → List (GLetter α)) (U P : List (GDRule α)) (π : GDRule α)
    (ha : ∀ n, dom n → ∃ es, GDChain U P es (E n) (E (f n)) ∧ cnt n ≤ es.count (GLabel.root π))
    (hc : AutoUseG f dom cnt)
    {d : ℕ} (hd : 0 < d) (J : GLetter α → AffFun ArcZ d)
    (hb : ∃ (D : ℕ) (u : Fin D → ArcZ) (A : Letter → Matrix (Fin D) (Fin D) ArcZ)
      (c : Fin D → ArcZ), ∀ n, gV hd J (E n) = autoValZ u A c n)
    (hlow : ∃ B : ℤ, ∀ n, ArcZ.fin B ≤ gV hd J (E n))
    (hU : ∀ ρ ∈ U, WeakA (gevA J ρ.lhs) (gevA J ρ.rhs))
    (hP : ∀ π' ∈ P, WeakTop hd (gevA J π'.lhs) (gevA J π'.rhs)) :
    ¬ StrictTop hd (gevA J π.lhs) (gevA J π.rhs) := by
  intro hs
  obtain ⟨D, u, A, c, hval⟩ := hb
  obtain ⟨B, hB⟩ := hlow
  have hsh : ∀ n, autoValZ (ArcZ.fin (-B) • u) A c n = ArcZ.fin (-B) * gV hd J (E n) := by
    intro n
    rw [autoValZ_smul, hval]
  refine barrier_of_auto_arcZG (autoCoreG_of_use hc) (ArcZ.fin (-B) • u) A c σ₀
    (List.mem_singleton_self _) ?_ ?_
  · intro n
    rw [hsh]
    have h := ArcticOrder.mul_mono (le_refl (ArcZ.fin (-B))) (hB n)
    rw [ArcZ.fin_mul_fin, neg_add_cancel] at h
    exact ArcZ.exists_nat_of_le h
  · intro n hn
    rw [count_cdOf, hsh, hsh, mul_assoc]
    refine ArcticOrder.mul_mono le_rfl ?_
    obtain ⟨es, hch, hle⟩ := ha n hn
    have h1 := gV_chain hd J (ArcZ.fin 1) (fun _ _ h => ArcZ.gg_mul_fin_one h) hU hP hs hch
    refine le_trans (ArcticOrder.mul_mono le_rfl ?_) h1
    rw [ArcZ.fin_pow, ArcZ.fin_pow, ArcZ.fin_le_fin]
    exact_mod_cast Nat.mul_le_mul_right 1 hle

/-! ## Family form (combined with Corollary 8.1) -/

/-- **Lemma 5.6, family form (`𝔸_ℕ`)**: (c) is obtained by Corollary 8.1 from the window frequencies and the numbers of uses along family orbits
(condition (c) of the paper). Condition (a) is needed only at points of family orbits (`famDom M`). -/
theorem simulation_family_arc (M : BlockModel) (hTW : HTerrasWinR M.R) {cnt : ℕ → ℕ}
    (hUse : HUseC M.f M.R M.steps cnt)
    (E : ℕ → List (GLetter α)) (U P : List (GDRule α)) (π : GDRule α)
    (ha : ∀ n, famDom M n →
      ∃ es, GDChain U P es (E n) (E (M.f n)) ∧ cnt n ≤ es.count (GLabel.root π))
    {d : ℕ} (hd : 0 < d) (J : GLetter α → AffFun Arc d)
    (hb : ∃ (D : ℕ) (u : Fin D → Arc) (A : Interp D) (c : Fin D → Arc),
      ∀ n, gV hd J (E n) = autoVal u A c n)
    (hfin : ∀ n, gV hd J (E n) ≠ 0)
    (hU : ∀ ρ ∈ U, WeakA (gevA J ρ.lhs) (gevA J ρ.rhs))
    (hP : ∀ π' ∈ P, WeakTop hd (gevA J π'.lhs) (gevA J π'.rhs)) :
    ¬ StrictTop hd (gevA J π.lhs) (gevA J π.rhs) :=
  simulation_arc E U P π ha (autoUseG_family M cnt hsp_holds hTW hUse) hd J hb hfin hU hP

/-- **Lemma 5.6, family form (below zero)**. -/
theorem simulation_family_arcZ (M : BlockModel) (hTW : HTerrasWinR M.R) {cnt : ℕ → ℕ}
    (hUse : HUseC M.f M.R M.steps cnt)
    (E : ℕ → List (GLetter α)) (U P : List (GDRule α)) (π : GDRule α)
    (ha : ∀ n, famDom M n →
      ∃ es, GDChain U P es (E n) (E (M.f n)) ∧ cnt n ≤ es.count (GLabel.root π))
    {d : ℕ} (hd : 0 < d) (J : GLetter α → AffFun ArcZ d)
    (hb : ∃ (D : ℕ) (u : Fin D → ArcZ) (A : Letter → Matrix (Fin D) (Fin D) ArcZ)
      (c : Fin D → ArcZ), ∀ n, gV hd J (E n) = autoValZ u A c n)
    (hlow : ∃ B : ℤ, ∀ n, ArcZ.fin B ≤ gV hd J (E n))
    (hU : ∀ ρ ∈ U, WeakA (gevA J ρ.lhs) (gevA J ρ.rhs))
    (hP : ∀ π' ∈ P, WeakTop hd (gevA J π'.lhs) (gevA J π'.rhs)) :
    ¬ StrictTop hd (gevA J π.lhs) (gevA J π.rhs) :=
  simulation_arcZ E U P π ha (autoUseG_family M cnt hsp_holds hTW hUse) hd J hb hlow hU hP

end Collatz.Arctic.DPGen
