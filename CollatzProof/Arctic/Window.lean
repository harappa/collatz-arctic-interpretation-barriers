/-
Definition of window frequencies (paragraph "Window frequencies" of Section 6.3): the empirical distribution of the windows of length `J` inside an interval
is within total variation distance `δ` of the uniform distribution on `{0,1}^J`.

* Digits are written as `Letter.f` (0) and `Letter.t` (1) (the words of `binTail` and `bitsMSB`).
* No probability is used; everything is finite counting (rational proportions).
-/
import CollatzProof.Arctic.Statement

namespace Collatz.Arctic

/-- All binary words of length `J` (sequences of `f` and `t`). -/
def wordsOfLen (J : ℕ) : Finset Word :=
  (Finset.univ : Finset (Fin J → Bool)).image
    (fun g => List.ofFn (fun i => if g i then Letter.t else Letter.f))

/-- The window of length `J` of the word `w` starting at position `a`. -/
def window (w : Word) (a J : ℕ) : Word := (w.drop a).take J

/-- The start positions of the windows of length `J` inside the interval `[a, b)` (`a, a+1, …, b-J`); there are `b + 1 - J - a` of them when `a + J ≤ b`. -/
def winStarts (a b J : ℕ) : List ℕ := (List.range (b + 1 - J - a)).map (fun i => a + i)

/-- The number of windows of length `J` in the interval `[a, b)` that are equal to the word `v`. -/
def winCount (w : Word) (a b J : ℕ) (v : Word) : ℕ :=
  ((winStarts a b J).filter (fun i => window w i J = v)).length

/-- **Window frequencies close to uniform**: `[a, b)` lies inside `w`, there is at least one window of length `J`, and the empirical distribution of the windows
is within total variation distance (half the sum of absolute differences) `δ` of the uniform distribution on `{0,1}^J`. -/
def WinClose (w : Word) (a b J : ℕ) (δ : ℚ) : Prop :=
  a + J ≤ b ∧ b ≤ w.length ∧
    (∑ v ∈ wordsOfLen J,
      |((winCount w a b J v : ℚ) / ((b + 1 - J - a : ℕ) : ℚ)) - 1 / 2 ^ J|) ≤ 2 * δ

end Collatz.Arctic
