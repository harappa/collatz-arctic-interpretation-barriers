/-
Events on the side of `t` for the assembly of Theorem 6.8 of the paper: the events (E1), (E2) and (E4) in the proof of Theorem 6.8.
Written as uniform counts over the free bits `x ∈ [0, 2^F)`.
* `cfg_count`: for at least `2^(F-L)` values of `x` the configuration at the starting point is that of the minimizing state `X_lo` (event (E1)).
* `win_count`: the window frequencies on each interval of the free bits are close to uniform (event (E2), the part at the starting point).
* `occ_count`: the digit word `w₀` occurs in the word of the free bits (used for the absorption at the end point, event (E4)).
-/
import CollatzProof.Arctic.CoreStart
import CollatzProof.Arctic.CoreLowerApp
import CollatzProof.Arctic.WindowLLN3

namespace Collatz.Arctic

open MinIdeal Classical

variable {D : ℕ}

/-- The configuration is given by a run of the support DFA. -/
theorem cfgOf_eq_run (A : Interp D) {E : BRel (Fin D)} (hE : E * E = E) (y₁ : Word) (hy : IsDigits y₁)
    (Y : Finset (Fin D)) :
    cfgOf A hE y₁ Y = hitSet hE ↑(Dfa.run (supDelta A) Y (y₁.map toBool)) := by
  unfold cfgOf
  rw [suppRel_ev_digits A y₁ hy, supRun_coe]

lemma isDigits_append {w w' : Word} (h : IsDigits w) (h' : IsDigits w') : IsDigits (w ++ w') := by
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · exact h s hs
  · exact h' s hs

/-- Transfer the count over the free bits to a count over `Fin F → Bool`. -/
theorem card_range_bits (F : ℕ) (Q : List Bool → Prop) [DecidablePred Q] :
    ((Finset.range (2 ^ F)).filter (fun x => Q ((bitsMSB F x).map toBool))).card =
      ((Finset.univ : Finset (Fin F → Bool)).filter (fun g => Q (List.ofFn g))).card := by
  rw [card_filter_bitsMSB F (fun w => Q (w.map toBool)), card_filter_wordsOfLen_toBool]

/-- **Event (E1)**: free bits for which the configuration at the starting point is that of the minimizing state `X_lo`. -/
theorem cfg_count (A : Interp D) (u₀ : Fin D → Arc) {E : BRel (Fin D)} (hE : E * E = E)
    (wstar : List Bool)
    (hw : ∀ q₀, Dfa.Recurrent (supDelta A) q₀ → ∀ (i : ZMod (Dfa.period (supDelta A) q₀))
      (v : List Bool), Dfa.img (supDelta A) (v ++ wstar) (Dfa.classSet (supDelta A) q₀ i) =
        Dfa.img (supDelta A) wstar (Dfa.classSet (supDelta A) q₀ (i + v.length)))
    {Xlo : Finset (Fin D)} (hrec : Dfa.Recurrent (supDelta A) Xlo) :
    ∃ L : ℕ, ∀ (pre S₁ v : Word) (F : ℕ), IsDigits pre → IsDigits S₁ → IsDigits v →
      Dfa.run (supDelta A) (suppF u₀) (pre.map toBool) = Xlo →
      L ≤ F → ((F + v.length : ℕ) : ZMod (Dfa.period (supDelta A) Xlo)) = 0 →
      2 ^ (F - L) ≤ ((Finset.range (2 ^ F)).filter (fun x =>
        cfgOf A hE (S₁ ++ wstar.map ofBool) (suppF (vecAfter u₀ A (pre ++ bitsMSB F x ++ v))) =
          cfgOf A hE (S₁ ++ wstar.map ofBool) Xlo)).card := by
  obtain ⟨L, hL⟩ := Dfa.start_count (supDelta A) wstar hw hrec
  refine ⟨L, fun pre S₁ v F hpre hS₁ hv hrun hLF hper => ?_⟩
  have hvlen : (v.map toBool).length = v.length := List.length_map _
  have h := hL (S₁.map toBool) (v.map toBool) F hLF (by rw [hvlen]; exact hper)
  have e := card_range_bits F (fun b => Dfa.run (supDelta A) (Dfa.run (supDelta A) Xlo b)
      (v.map toBool ++ S₁.map toBool ++ wstar) =
    Dfa.run (supDelta A) Xlo (S₁.map toBool ++ wstar))
  replace h : 2 ^ (F - L) ≤ ((Finset.range (2 ^ F)).filter (fun x =>
      Dfa.run (supDelta A) (Dfa.run (supDelta A) Xlo ((bitsMSB F x).map toBool))
        (v.map toBool ++ S₁.map toBool ++ wstar) =
      Dfa.run (supDelta A) Xlo (S₁.map toBool ++ wstar))).card := by
    rw [e]; exact h
  refine le_trans h (Finset.card_le_card ?_)
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  refine ⟨hx.1, ?_⟩
  have hdig : IsDigits (pre ++ bitsMSB F x ++ v) :=
    isDigits_append (isDigits_append hpre (bitsMSB_isDigits F x)) hv
  have hy : IsDigits (S₁ ++ wstar.map ofBool) := isDigits_append hS₁ (isDigits_ofBool wstar)
  rw [cfgOf_eq_run A hE _ hy, cfgOf_eq_run A hE _ hy, suppF_vecAfter_run u₀ A _ hdig]
  congr 2
  simp only [List.map_append, map_toBool_ofBool, Dfa.run_append, hrun]
  rw [← Dfa.run_append, ← Dfa.run_append, ← List.append_assoc] at *
  simpa [Dfa.run_append, List.append_assoc] using hx.2

/-- **Windows of the free bits**: there are at most `ε 2^F` free bits for which the window frequencies on an interval of length at least `M₀`
(`[a, b) ⊆ [0, F)`) are not close to uniform. -/
theorem win_bad_count (J : ℕ) (δ ε : ℚ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ F a b : ℕ, a ≤ b → b ≤ F → M₀ ≤ b - a →
      (((Finset.range (2 ^ F)).filter (fun x => ¬ WinClose (bitsMSB F x) a b J δ)).card : ℚ) ≤
        ε * 2 ^ F := by
  obtain ⟨M₀, hM⟩ := winClose_lln_interval J δ ε hδ hε
  refine ⟨M₀, fun F a b hab hbF hM₀ => ?_⟩
  have h := hM F a b hab hbF hM₀
  have e : ((Finset.range (2 ^ F)).filter (fun x => ¬ WinClose (bitsMSB F x) a b J δ)).card =
      ((wordsOfLen F).filter (fun w => ¬ WinClose w a b J δ)).card := by
    exact card_filter_bitsMSB F (fun w => ¬ WinClose w a b J δ)
  rw [e]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := wordsOfLen F) (fun w => WinClose w a b J δ)
  rw [card_wordsOfLen] at hsplit
  have : (((wordsOfLen F).filter (fun w => WinClose w a b J δ)).card : ℚ) +
      (((wordsOfLen F).filter (fun w => ¬ WinClose w a b J δ)).card : ℚ) = 2 ^ F := by
    exact_mod_cast hsplit
  linarith

/-- **Occurrence of a word**: there are at most `ε 2^F` values of `x` for which the digit word `v ≠ []` does not occur in the interval `[a, b)` of the word of the free bits. -/
theorem noOcc_count {v : Word} (hv : IsDigits v) (hne : v ≠ []) (ε : ℚ) (hε : 0 < ε) :
    ∃ D₀ : ℕ, ∀ F a b : ℕ, b ≤ F → a + D₀ ≤ b →
      (((Finset.range (2 ^ F)).filter (fun x => ∀ i, a ≤ i → i + v.length ≤ b →
        window (bitsMSB F x) i v.length ≠ v)).card : ℚ) ≤ ε * 2 ^ F := by
  obtain ⟨D₀, hD⟩ := noOcc_small (mem_wordsOfLen_of rfl hv) hne ε hε
  refine ⟨D₀, fun F a b hbF hab => ?_⟩
  have e : ((Finset.range (2 ^ F)).filter (fun x => ∀ i, a ≤ i → i + v.length ≤ b →
      window (bitsMSB F x) i v.length ≠ v)).card = ((wordsOfLen F).filter
      (fun w => ∀ i, a ≤ i → i + v.length ≤ b → window w i v.length ≠ v)).card := by
    exact card_filter_bitsMSB F (fun w => ∀ i, a ≤ i → i + v.length ≤ b → window w i v.length ≠ v)
  rw [e]
  exact hD F a b hbF hab

end Collatz.Arctic
