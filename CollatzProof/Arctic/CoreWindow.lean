/-
Locality of window frequencies (assembly of Theorem 6.8 of the paper): the window frequencies on an interval `[a, b)` depend only on the digits in that interval.
The window frequencies of the word `p ++ w ++ q` on the interval `[|p| + a, |p| + b)` equal those of `w` on the interval `[a, b)`.
Used to transfer the window frequencies of each part to the partition of the digits of the starting point (`τ`, free bits, `ρ`, Terras part, shared part).
-/
import CollatzProof.Arctic.RateUpperBase

namespace Collatz.Arctic

theorem window_append_shift (p w q : Word) {i J : ℕ} (h : i + J ≤ w.length) :
    window (p ++ w ++ q) (p.length + i) J = window w i J := by
  unfold window
  rw [List.append_assoc, List.drop_length_add_append, List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by rw [List.length_drop]; omega)]

theorem winCount_append_shift (p w q : Word) {a b J : ℕ} (hb : b ≤ w.length) (v : Word) :
    winCount (p ++ w ++ q) (p.length + a) (p.length + b) J v = winCount w a b J v := by
  rw [winCount_eq_card, winCount_eq_card]
  have e : p.length + b + 1 - J - (p.length + a) = b + 1 - J - a := by omega
  rw [e]
  congr 1
  apply Finset.filter_congr
  intro i hi
  rw [Finset.mem_range] at hi
  rw [show p.length + a + i = p.length + (a + i) by omega,
    window_append_shift p w q (by omega)]

theorem winClose_append_shift (p w q : Word) {a b J : ℕ} (hb : b ≤ w.length) (δ : ℚ) :
    WinClose (p ++ w ++ q) (p.length + a) (p.length + b) J δ ↔ WinClose w a b J δ := by
  unfold WinClose
  have e : p.length + b + 1 - J - (p.length + a) = b + 1 - J - a := by omega
  simp only [winCount_append_shift p w q hb, e, List.length_append]
  constructor
  · rintro ⟨h1, -, h3⟩; exact ⟨by omega, hb, h3⟩
  · rintro ⟨h1, -, h3⟩; exact ⟨by omega, by omega, h3⟩

end Collatz.Arctic
