/-
Definitions for the model of $H$, and the interface statements between the parts of the formalization. **The statements are frozen.**
They are shared by the system $\mathcal H$ (collatz-T-5or7mod8) and the system $R_H$.

* The map `Hmap`: the map $H$ of Conjecture 4.14 of Yolcu–Aaronson–Heule 2023 ($3n/4$ for $n \equiv 0 \bmod 4$, $(9n+1)/8$ for $n \equiv 7 \bmod 8$). Outside the domain it is
  the identity (its values outside the domain affect no statement; every use is guarded by `HDom`).
* `HDom`: the points at which canonical derivations are used (the condition $x \ge 8$). $n = 7$ is excluded, since no dynamic
  rule applies to `can 7 = /tt.`.
* The Terras correspondence (letter words, `true` = $\mathsf a$, `false` = $\mathsf b$): the state $(m, r, c, a)$ is built one letter at a time. If the next letter is $\mathsf a$
  (resp. $\mathsf b$), the low digits $t_0$ of $t$ with $c + 3^a t_0 \equiv 0 \pmod 4$ (resp. $\equiv 7 \pmod 8$) (`tA`, `tB`; $3^a \bmod 8$ is
  `pow3mod8 a`, and $3^{-a} \equiv 3^a \pmod 8$) are added to $r$. The invariant is $H^{\lvert w\rvert}(r + 2^m t) = c + 3^a t$.
* Blocks (the model of Proposition 7.2): $X = \mathsf{abb}$ (8 bits, exponent 5 of 3), $Y = \mathsf{abbb}$ (11 bits, exponent 7). They have the same shape as the blocks $X'$, $Y'$
  of $T$, so the number of bits and the exponent of 3 are given by `parityOf` (proved in `HModel/Terras2.lean`). The number of steps `hSteps β` is 3 or 4 per block.
* Interface statements (proved in `HModel/Terras2.lean` and `HModel/Swap.lean`, used as hypotheses by the parts on uses of rules and by the assembly): `SpecHModel` (the fields of the model), `SpecHClass` (the residue
  classes along orbits), `SpecHBoundary` (the form of block boundary points), `SpecHSwap` (the swap, `e₂ = 8`, `e₃ = 8`).
-/
import CollatzProof.Arctic.Gen.Model

namespace Collatz.Arctic.HModel

open Collatz.Arctic

/-! ## The map and its domain -/

/-- The map $H$ (the identity outside its domain). -/
def Hmap (n : ℕ) : ℕ := if n % 4 = 0 then 3 * (n / 4) else if n % 8 = 7 then (9 * n + 1) / 8 else n

/-- The points at which canonical derivations are used ($x \ge 8$). -/
def HDom (n : ℕ) : Prop := 8 ≤ n ∧ (n % 4 = 0 ∨ n % 8 = 7)

/-! ## The Terras correspondence -/

/-- $3^a \bmod 8$ (determined by the parity of $a$). -/
def pow3mod8 (a : ℕ) : ℕ := if a % 2 = 0 then 1 else 3

/-- The low 2 digits of $t$ for a step $\mathsf a$: $c + 3^a\,t_A \equiv 0 \pmod 4$. -/
def tA (c a : ℕ) : ℕ := ((4 - c % 4) * pow3mod8 a) % 4

/-- The low 3 digits of $t$ for a step $\mathsf b$: $c + 3^a\,t_B \equiv 7 \pmod 8$. -/
def tB (c a : ℕ) : ℕ := ((15 - c % 8) * pow3mod8 a) % 8

/-- One step of the Terras correspondence (state $(m, r, c, a)$, `true` = $\mathsf a$, `false` = $\mathsf b$). -/
def hStep (s : ℕ × ℕ × ℕ × ℕ) (x : Bool) : ℕ × ℕ × ℕ × ℕ :=
  if x then (s.1 + 2, s.2.1 + 2 ^ s.1 * tA s.2.2.1 s.2.2.2,
      Hmap (s.2.2.1 + 3 ^ s.2.2.2 * tA s.2.2.1 s.2.2.2), s.2.2.2 + 1)
  else (s.1 + 3, s.2.1 + 2 ^ s.1 * tB s.2.2.1 s.2.2.2,
      Hmap (s.2.2.1 + 3 ^ s.2.2.2 * tB s.2.2.1 s.2.2.2), s.2.2.2 + 2)

/-- The state $(m_w, r_w, c_w, a_w)$ of a letter word. -/
def hState (w : List Bool) : ℕ × ℕ × ℕ × ℕ := w.foldl hStep (0, 0, 0, 0)

/-- A block sequence as a letter word (`true` = $X = \mathsf{abb}$, `false` = $Y = \mathsf{abbb}$). -/
def lettersOf (β : List Bool) : List Bool :=
  β.flatMap (fun x => if x then [true, false, false] else [true, false, false, false])

/-- The Terras residue $r_\beta$ of the block sequence `β`. -/
def hR (β : List Bool) : ℕ := (hState (lettersOf β)).2.1

/-- The end-point constant $c_\beta$. -/
def hC (β : List Bool) : ℕ := (hState (lettersOf β)).2.2.1

/-- The number of steps (the number of letters). -/
def hSteps (β : List Bool) : ℕ := (lettersOf β).length

/-! ## Checks on small values -/

example : Hmap 12 = 9 ∧ Hmap 15 = 17 ∧ Hmap 5 = 5 := by decide
example : hState (lettersOf [true]) = (8, 84, 80, 5) := by decide
example : hState (lettersOf [false]) = (11, 1364, 1457, 7) := by decide
example : hSteps [true, false] = 7 := by decide
/-- The number of bits and the exponent of 3 agree with the form for $T$ (`parityOf`) (a small example). -/
example : (hState (lettersOf [true, false, false, true])).1 = (parityOf [true, false, false, true]).length ∧
    (hState (lettersOf [true, false, false, true])).2.2.2 = terrasA (parityOf [true, false, false, true]) := by
  decide
/-- A small example of the Terras correspondence: $84 + 256 \cdot 5$, which follows $X$, reaches $80 + 243 \cdot 5$ in 3 steps. -/
example : Hmap^[3] (84 + 256 * 5) = 80 + 243 * 5 := by decide

/-! ## Interface statements -/

/-- Interface statement: the fields of the model (the material for building a `Gen.BlockModel`). -/
structure SpecHModel : Prop where
  R_lt : ∀ β, hR β < 2 ^ (parityOf β).length
  C_lt : ∀ β, hC β < 3 ^ terrasA (parityOf β)
  R_prefix : ∀ β₁ β₂, hR (β₁ ++ β₂) % 2 ^ (parityOf β₁).length = hR β₁
  iter : ∀ β t, Hmap^[hSteps β] (hR β + 2 ^ (parityOf β).length * t) = hC β + 3 ^ terrasA (parityOf β) * t
  orbit_dom : ∀ β t, 1 ≤ t → ∀ i < hSteps β, HDom (Hmap^[i] (hR β + 2 ^ (parityOf β).length * t))
  f_pos : ∀ n, HDom n → 1 ≤ Hmap n

/-- The block model of $H$ obtained from `SpecHModel` (used in the assembly). -/
def modelOf (h : SpecHModel) : Gen.BlockModel where
  f := Hmap
  dom := HDom
  steps := hSteps
  R := hR
  C := hC
  R_lt := h.R_lt
  C_lt := h.C_lt
  R_prefix := h.R_prefix
  iter := h.iter
  orbit_dom := h.orbit_dom
  f_pos := h.f_pos

/-- Interface statement: the residue classes along orbits ($\equiv 0 \pmod 4$ if the `i`-th letter is $\mathsf a$, $\equiv 7 \pmod 8$ if it is $\mathsf b$). -/
def SpecHClass : Prop := ∀ (β : List Bool) (t i : ℕ), i < hSteps β →
  if (lettersOf β).getD i false then Hmap^[i] (hR β + 2 ^ (parityOf β).length * t) % 4 = 0
  else Hmap^[i] (hR β + 2 ^ (parityOf β).length * t) % 8 = 7

/-- Interface statement: the form of block boundary points. The boundary point is the point of the orbit after `hSteps (β.take i)` steps, and
`blockEnd β i` is the number of bits up to it. $P_i = c_{\beta_{<i}} + 3^{a_i}(r' + 2^{m - L_i} t)$ with $r' < 2^{m - L_i}$. -/
def SpecHBoundary : Prop := ∀ (β : List Bool) (t i : ℕ), i < β.length →
  ∃ r' < 2 ^ ((parityOf β).length - blockEnd β i),
    Hmap^[hSteps (β.take i)] (hR β + 2 ^ (parityOf β).length * t)
      = hC (β.take i) + 3 ^ terrasA (parityOf (β.take i)) *
          (r' + 2 ^ ((parityOf β).length - blockEnd β i) * t)

/-- Interface statement: the translation by a swap (the $H$ version of Lemma B.5 (ii), `e₂ = 8`, `e₃ = 8`). -/
def SpecHSwap : Prop := Gen.SwapR hR 8 8

end Collatz.Arctic.HModel
