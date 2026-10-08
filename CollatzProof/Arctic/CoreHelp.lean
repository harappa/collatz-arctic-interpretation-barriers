/-
Small lemmas for the assembly of Theorem 6.8 of the paper: lengths of blocks, the top window `τ`, counting through a bijection,
adjusting to the period.
-/
import CollatzProof.Arctic.CoreConfig
import CollatzProof.Arctic.CoreLowerApp
import CollatzProof.Arctic.Family

namespace Collatz.Arctic

/-- The length of the parity word is between 8 and 11 times the number of blocks. -/
theorem parityOf_length_bounds (β : List Bool) :
    8 * β.length ≤ (parityOf β).length ∧ (parityOf β).length ≤ 11 * β.length := by
  induction β with
  | nil => simp [parityOf]
  | cons x β ih =>
    have e : parityOf (x :: β) = (if x then blkX else blkY) ++ parityOf β := by
      simp [parityOf]
    rw [e, List.length_append, List.length_cons]
    cases x <;> simp [blkX, blkY] <;> omega

/-- For the number `τ = 2^p + val(w)` that places the digit word `w` (of length `p`) after the leading 1, `bin'` is `w`. -/
theorem binTail_tau (w : List Bool) :
    binTail (2 ^ w.length + valMSB (w.map ofBool)) = w.map ofBool := by
  have hmem : w.map ofBool ∈ wordsOfLen w.length :=
    mem_wordsOfLen_of (by simp) (isDigits_ofBool w)
  rw [← image_bitsMSB] at hmem
  obtain ⟨r, hr, hrw⟩ := Finset.mem_image.mp hmem
  have hr' := Finset.mem_range.mp hr
  rw [← hrw, valMSB_bitsMSB _ _ hr', add_comm, ← bitsMSB_eq_binTail _ _ hr']

theorem tau_bounds (w : List Bool) :
    2 ^ (w.length + 1 - 1) ≤ 2 ^ w.length + valMSB (w.map ofBool) ∧
      2 ^ w.length + valMSB (w.map ofBool) < 2 ^ (w.length + 1) := by
  have hmem : w.map ofBool ∈ wordsOfLen w.length :=
    mem_wordsOfLen_of (by simp) (isDigits_ofBool w)
  rw [← image_bitsMSB] at hmem
  obtain ⟨r, hr, hrw⟩ := Finset.mem_image.mp hmem
  have hr' := Finset.mem_range.mp hr
  rw [← hrw, valMSB_bitsMSB _ _ hr', Nat.add_sub_cancel, pow_succ]
  omega

/-- Counting through a bijection: if `f` is a bijection on `range N`, the number of elements satisfying `P ∘ f` equals the number satisfying `P`. -/
theorem card_filter_comp_bij (N : ℕ) (f : ℕ → ℕ)
    (hf : Set.BijOn f ↑(Finset.range N) ↑(Finset.range N)) (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range N).filter (fun x => P (f x))).card = ((Finset.range N).filter P).card := by
  have himg : ((Finset.range N).filter (fun x => P (f x))).image f = (Finset.range N).filter P := by
    ext y
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨x, ⟨hx, hpx⟩, rfl⟩
      exact ⟨Finset.mem_coe.mp (hf.mapsTo (Finset.mem_coe.mpr hx)), hpx⟩
    · rintro ⟨hy, hpy⟩
      obtain ⟨x, hx, rfl⟩ := hf.surjOn (Finset.mem_coe.mpr hy)
      exact ⟨x, ⟨Finset.mem_coe.mp hx, hpy⟩, rfl⟩
  rw [← himg, Finset.card_image_of_injOn]
  exact hf.injOn.mono (fun x hx => Finset.mem_coe.mpr (Finset.mem_of_mem_filter _ (Finset.mem_coe.mp hx)))

/-- Adjusting to the period: with `j := (P - x % P) % P` we have `P ∣ x + j` and `j < P`. -/
theorem period_align (P x : ℕ) (hP : 0 < P) : (x + (P - x % P) % P) % P = 0 ∧ (P - x % P) % P < P := by
  refine ⟨?_, Nat.mod_lt _ hP⟩
  have h1 := Nat.mod_lt x hP
  rcases Nat.eq_zero_or_pos (x % P) with h0 | h0
  · rw [h0, Nat.sub_zero, Nat.mod_self, add_zero]; exact h0
  · rw [Nat.mod_eq_of_lt (by omega : P - x % P < P)]
    have := Nat.mod_add_div x P
    rw [show x + (P - x % P) = P * (x / P + 1) by
      rw [mul_add, mul_one]; omega]
    exact Nat.mul_mod_right _ _

end Collatz.Arctic
