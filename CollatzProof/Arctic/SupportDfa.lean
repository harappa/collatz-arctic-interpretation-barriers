/-
The support DFA: the forward support process of the automaton read as a general DFA of `Dfa.lean`.
The forward support DFA `𝒜` (subset construction) of the proof of Theorem 6.8 (Section 6.5).

* The states are sets of indices `Finset (Fin D)`; the digit `b` acts by `X ↦ X·B_b` (`B_b` is the support of the digit matrix, `N̄_b` in the paper).
* `supRun_coe`: the run of the DFA equals the support process given by `act` and `typ` (`Transport.lean`, `TransportStay.lean`).
* `suppF_vecAfter_run`: the support of the value vector after reading a digit word is the run of the DFA.
-/
import CollatzProof.Arctic.ConfigLemmas
import CollatzProof.Arctic.Dfa2

namespace Collatz.Arctic

open MinIdeal Matrix

variable {D : ℕ}

open Classical in
/-- One step of the support DFA: `X ↦ X·B_b`. -/
noncomputable def supDelta (A : Interp D) (X : Finset (Fin D)) (b : Bool) : Finset (Fin D) :=
  Finset.univ.filter (fun k => ∃ s ∈ X, letter (B0 A) (B1 A) b s k)

theorem coe_supDelta (A : Interp D) (X : Finset (Fin D)) (b : Bool) :
    ((supDelta A X b : Finset (Fin D)) : Set (Fin D)) = act ↑X (letter (B0 A) (B1 A) b) := by
  ext k
  simp [supDelta, act]

/-- The run of the support DFA is the support process `S ↦ S·typ w` of `TransportStay.lean`. -/
theorem supRun_coe (A : Interp D) :
    ∀ (w : List Bool) (X : Finset (Fin D)),
      ((Dfa.run (supDelta A) X w : Finset (Fin D)) : Set (Fin D)) = act ↑X (typ (B0 A) (B1 A) w)
  | [], X => by simp [Dfa.run, typ_nil, act_one]
  | b :: w, X => by
    rw [Dfa.run_cons, supRun_coe A w, coe_supDelta]
    have : typ (B0 A) (B1 A) (b :: w) = letter (B0 A) (B1 A) b * typ (B0 A) (B1 A) w := by
      simp [typ]
    rw [this, act_mul]

open Classical in
/-- The support of a value vector (as a `Finset`). -/
noncomputable def suppF (v : Fin D → Arc) : Finset (Fin D) := Finset.univ.filter (fun j => v j ≠ 0)

theorem coe_suppF (v : Fin D → Arc) : ((suppF v : Finset (Fin D)) : Set (Fin D)) = suppV v := by
  ext j; simp [suppF, suppV]

/-- The support of the value vector after reading a digit word is the run of the support DFA. -/
theorem suppF_vecAfter_run (u : Fin D → Arc) (A : Interp D) (w : Word) (hw : IsDigits w) :
    suppF (vecAfter u A w) = Dfa.run (supDelta A) (suppF u) (w.map toBool) := by
  apply Finset.coe_injective
  rw [coe_suppF, supRun_coe, suppV_vecAfter, coe_suppF, suppRel_ev_digits A w hw]

end Collatz.Arctic
