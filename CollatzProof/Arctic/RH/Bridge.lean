/-
The bridge for the system $R_H$ (Lemma 5.2 for $R_H$; Section 7).
Proves **`specBridgeRH : SpecBridgeRH`** (the frozen statement in `RH/Spec.lean`).

* `phi_canRH_eq_autoVal`: `Φ(canRH n) = autoVal u I c n`. Since `canRH n = L t bin'(n) .` contains the leading one as the symbol `t`,
  the start vector is `u` = row 0 of `(I L ⊗ I t)` (in `AutoBridge.phi_can_eq_autoVal` for $\mathcal T$ and $\mathcal H$
  it is row 0 of `I /`), and the end vector is column 0 of `I .`. Since `AutoCoreG` speaks about all automata
  `(u, A, c)`, it suffices to choose `u` here.
* `orbit_boundRH`, `specBridgeRH`: copies of `orbit_boundG` and `barrier_of_autoCoreG` of `Gen/SysBridge.lean` with `can` replaced by `canRH`
  (the map, domain, rules and canonical derivations remain parameters; the proofs are those of the original).
-/
import CollatzProof.Arctic.RH.Spec
import CollatzProof.Arctic.Gen.SysBridge

namespace Collatz.Arctic.RH

open Collatz.Arctic Matrix

/-- `Φ(canRH n)` is an automaton value (`u` = row 0 of `I L ⊗ I t`, `A = I`, `c` = column 0 of `I .`). -/
lemma phi_canRH_eq_autoVal {d : ℕ} (hd : 0 < d) (I : Interp d) (n : ℕ) :
    Phi hd I (canRH n) = autoVal (fun j => (I Letter.lft * I Letter.t) ⟨0, hd⟩ j) I
      (fun j => I Letter.rgt j ⟨0, hd⟩) n := by
  unfold Phi canRH autoVal
  rw [ev_cons, ev_cons, ev_append, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.dotProduct_mulVec,
    Matrix.mul_apply]
  have h1 : ev I [Letter.rgt] = I Letter.rgt := by simp [ev]
  rw [h1]
  simp only [dotProduct, Matrix.vecMul, Matrix.mul_apply]

/-- One step of the number of uses along an orbit segment (a copy of a `private` lemma of `Gen/SysBridge.lean`). -/
private theorem usesOrbitG_succRH (f : ℕ → ℕ) (cd : ℕ → List Rule) (ρ : Rule) (n m : ℕ) :
    Gen.usesOrbitG f cd ρ n (m + 1) = (cd n).count ρ + Gen.usesOrbitG f cd ρ (f n) m := by
  simp only [Gen.usesOrbitG, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  congr 2

/-- Estimate along orbits (the `canRH` version of `Gen.orbit_boundG`): `Φ` decreases at least by the number of uses of a strictly oriented rule `ρ`. -/
theorem orbit_boundRH {f : ℕ → ℕ} {dom : ℕ → Prop} {rules : List Rule} {cd : ℕ → List Rule}
    (hchain : ∀ n, dom n → Chain (cd n) (canRH n) (canRH (f n)))
    (hsub : ∀ n, dom n → ∀ σ ∈ cd n, σ ∈ rules)
    {d : ℕ} (hd : 0 < d) (I : Interp d) (hfin : Fin00 hd I)
    (hweak : ∀ ρ ∈ rules, Weak I ρ) {ρ : Rule} (hρ : Strict I ρ) :
    ∀ (m n : ℕ), (∀ i < m, dom (f^[i] n)) → ∀ a b : ℕ, Phi hd I (canRH n) = Arc.fin a →
      Phi hd I (canRH (f^[m] n)) = Arc.fin b → b + Gen.usesOrbitG f cd ρ n m ≤ a := by
  intro m
  induction m with
  | zero =>
    intro n _ a b ha hb
    simp only [Function.iterate_zero, id] at hb
    rw [ha] at hb
    have hab : a = b := Arc.fin_inj hb
    simp [Gen.usesOrbitG, hab]
  | succ m ih =>
    intro n horb a b ha hb
    have hn : dom n := by simpa using horb 0 (Nat.succ_pos m)
    obtain ⟨c, hc⟩ := phi_fin hd I hfin (canRH (f n))
    have hstep := phi_chain hd I hfin hρ (hchain n hn)
      (fun σ hσ => hweak σ (hsub n hn σ hσ)) a c ha hc
    have horb' : ∀ i < m, dom (f^[i] (f n)) := by
      intro i hi
      have := horb (i + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    have hb' : Phi hd I (canRH (f^[m] (f n))) = Arc.fin b := by
      rwa [← Function.iterate_succ_apply]
    have hrest := ih (f n) horb' c b hc hb'
    rw [usesOrbitG_succRH]
    omega

/-- **Output of this unit**: the frozen `SpecBridgeRH` (the `canRH` version of `Gen.barrier_of_autoCoreG`). -/
theorem specBridgeRH : SpecBridgeRH := by
  intro f dom rules cd h hchain hsub d hd I hfin hweak ρ hρmem hρ
  have hval := phi_canRH_eq_autoVal hd I
  obtain ⟨n, -, m, horb, hlt⟩ := h d (fun j => (I Letter.lft * I Letter.t) ⟨0, hd⟩ j) I
    (fun j => I Letter.rgt j ⟨0, hd⟩) 0
    (by
      intro n _ h0
      rw [← hval] at h0
      exact phi_finite hd I hfin (canRH n) (by rw [h0]; rfl))
    (by
      intro n hn a b ha hb
      rw [← hval] at ha hb
      have := phi_chain_weak hd I (hchain n hn) (fun σ hσ => hweak σ (hsub n hn σ hσ))
      rw [ha, hb, Arc.fin_le_fin] at this
      omega)
    ρ hρmem 0
  rw [← hval] at hlt
  obtain ⟨a, ha⟩ := phi_fin hd I hfin (canRH n)
  obtain ⟨b, hb⟩ := phi_fin hd I hfin (canRH (f^[m] n))
  have hbound := orbit_boundRH hchain hsub hd I hfin hweak hρ m n horb a b ha hb
  rw [ha, Arc.fin_lt_fin] at hlt
  omega

end Collatz.Arctic.RH
