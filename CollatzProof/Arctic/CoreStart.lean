/-
The minimal configuration occurs with positive probability at the starting point (assembly of Theorem 6.8 of the paper). This is the start count in the proof
of Theorem 6.8: after the free bits of `t`, the state of `𝒜` takes each state of the cyclic class `C'` often enough (fact (A3)), and for the
subsequent word `v` given by `σ` we have `δ_{vw*}(C') = δ_{w*}(C)` (fact (A2)), so each value of `δ_y(C)` occurs often enough.

Written for a general DFA: from a recurrent state `q₁` read a free word of length `F`, then the fixed words `v`, `S₁`, `w*`.
If `F + |v|` is a multiple of the period, then for at least `2^(F-L)` of the free words the final state equals the state reached from `q₁` by reading `S₁ w*`.
-/
import CollatzProof.Arctic.Dfa2

namespace Collatz.Arctic.Dfa

variable {S : Type*} [Fintype S] [DecidableEq S] (δ : S → Bool → S)

theorem start_count (wstar : List Bool)
    (hw : ∀ q₀, Recurrent δ q₀ → ∀ (i : ZMod (period δ q₀)) (v : List Bool),
      img δ (v ++ wstar) (classSet δ q₀ i) = img δ wstar (classSet δ q₀ (i + v.length)))
    {q₁ : S} (hrec : Recurrent δ q₁) :
    ∃ L : ℕ, ∀ (S₁ v : List Bool) (F : ℕ), L ≤ F → ((F + v.length : ℕ) : ZMod (period δ q₁)) = 0 →
      2 ^ (F - L) ≤ ((Finset.univ : Finset (Fin F → Bool)).filter
        (fun g => run δ (run δ q₁ (List.ofFn g)) (v ++ S₁ ++ wstar) = run δ q₁ (S₁ ++ wstar))).card := by
  obtain ⟨L, hL⟩ := count_words hrec
  refine ⟨L, fun S₁ v F hF hper => ?_⟩
  -- the image of the states of class `F` is the image of class 0 (property of `w*`)
  have h1 := hw q₁ hrec ((F : ℕ) : ZMod (period δ q₁)) (v ++ S₁)
  have h2 := hw q₁ hrec 0 S₁
  have hidx : ((F : ℕ) : ZMod (period δ q₁)) + ((v ++ S₁).length : ℕ) = 0 + (S₁.length : ℕ) := by
    rw [List.length_append, Nat.cast_add, ← add_assoc, ← Nat.cast_add, hper, zero_add]
  rw [hidx, ← h2] at h1
  -- `run q₁ (S₁ w*)` lies in the right-hand side
  have hmem : run δ q₁ (S₁ ++ wstar) ∈ img δ (S₁ ++ wstar) (classSet δ q₁ 0) := by
    apply Finset.mem_image.mpr
    refine ⟨q₁, ?_, rfl⟩
    exact mem_classSet.mpr ⟨Reach.refl q₁, cls_self hrec⟩
  rw [← h1] at hmem
  obtain ⟨q', hq', hrun⟩ := Finset.mem_image.mp hmem
  obtain ⟨hreach, hcls⟩ := mem_classSet.mp hq'
  -- the number of words of length `F` from `q₁` to `q'`
  have hcnt := hL F hF q₁ q' (Reach.refl q₁) hreach (by rw [hcls, cls_self hrec, zero_add])
  refine le_trans hcnt (Finset.card_le_card ?_)
  intro g hg
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
  rw [hg]
  exact hrun

end Collatz.Arctic.Dfa
