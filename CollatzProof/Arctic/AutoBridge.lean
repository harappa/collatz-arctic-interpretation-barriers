/-
Derivation of `ValueCore` from `AutoCore`.

* `Statement.ValueCore` (the form for the canonical value `Φ(can n)`) is the case `κ = 0` of `AutoStatement.AutoCore` (the form for values of arctic automata
  reading binary digits): with `u` = row 0 of `I lft`, `A = I` and `c` = column 0 of `I rgt`, `Φ(can n) = autoVal u I c n`.
* Hence `Main.arctic_barrier_ST` also follows from `AutoCore` alone (`arctic_barrier_ST (valueCore_of_autoCore h)`).
-/
import CollatzProof.Arctic.Main
import CollatzProof.Arctic.AutoStatement

namespace Collatz.Arctic

open Matrix Arc

/-- `Φ(can n)` is a value of an automaton (`u` = row 0 of `I lft`, `A = I`, `c` = column 0 of `I rgt`). -/
lemma phi_can_eq_autoVal {d : ℕ} (hd : 0 < d) (I : Interp d) (n : ℕ) :
    Phi hd I (can n) = autoVal (fun j => I Letter.lft ⟨0, hd⟩ j) I
      (fun j => I Letter.rgt j ⟨0, hd⟩) n := by
  unfold Phi can autoVal
  rw [ev_cons, ev_append, ← Matrix.mul_assoc, Matrix.dotProduct_mulVec, Matrix.mul_apply]
  have h1 : ev I [Letter.rgt] = I Letter.rgt := by simp [ev]
  rw [h1]
  simp only [dotProduct, Matrix.vecMul, Matrix.mul_apply]

/-- `ValueCore` from `AutoCore` (`κ = 0`). Finiteness of the values comes from `Fin00` (`phi_finite`); non-increase along steps of `T`
is the hypothesis itself. -/
theorem valueCore_of_autoCore (h : AutoCore) : ValueCore := by
  intro d hd I hfin hmono ρ hρ N
  have hval := phi_can_eq_autoVal hd I
  obtain ⟨n, hn, m, horb, hlt⟩ := h d (fun j => I Letter.lft ⟨0, hd⟩ j) I
    (fun j => I Letter.rgt j ⟨0, hd⟩) 0
    (by
      intro n _ h0
      rw [← hval] at h0
      exact phi_finite hd I hfin (can n) (by rw [h0]; rfl))
    (by
      intro n hn a b ha hb
      rw [← hval] at ha hb
      have := hmono n hn
      rw [ha, hb, fin_le_fin] at this
      omega)
    ρ hρ N
  refine ⟨n, hn, m, horb, ?_⟩
  rw [hval]
  simpa using hlt

end Collatz.Arctic
