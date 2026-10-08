/-
The Lean basis of Proposition 9.5 of the paper (the natural-number example of Section 9): a natural-number affine interpretation of
dimension 4 showing that the hypothesis (P) (primitivity) of Theorem 4.1 and Proposition 6.1 of Paper II cannot be dropped. The conclusion itself
(the negation of the theorems of Paper II with (P) removed) is not formalized, since the theorems of Paper II are not in Lean; parts (i)-(iii) of the
proposition and the remark after it (the form of Paper I) are its basis. This file: the definitions and (i), (ii); `NatExample2.lean`: (iii), the remark and the summary theorems `prop_10_1_*`.

* Conventions (Section 2 of Paper II): `[s](y) = M_s y + v_s` (`M_s ∈ ℕ^{4×4}`, `v_s ∈ ℕ^4`), extended to strings by composition,
  `[s₁ ⋯ sₙ] = [s₁] ∘ ⋯ ∘ [sₙ]` (`evN_app`), and `Φ(w) = ([w](0))₁`. Indices start at 0 (index 1 of the paper is `0`, and the index
  `2 + r` of the residue `r` is `1 + r`). Weak orientation is coefficientwise, `M_ℓ ≥ M_r` and `v_ℓ ≥ v_r`; strict orientation follows (2) of Yolcu–Aaronson–Heule
  (the convention of Endrullis–Waldmann–Zantema 2008 and Hofbauer–Waldmann): weak orientation with a strictly larger first component of `v` (`NStrict`).
  In the example below the first components of `v` of the two sides agree for every rule (`v0_*`), so no rule is strictly oriented under any
  convention that asks the first component to decrease strictly at `y = 0`.
* The interpretation `interp r_in r_out`: `(M_b)₀₀ = 1`, `(M_b)_{1+r, 1+(2r+b mod 3)} = 2` (`f` = 0, `t` = 1), `(M_d)₀₀ = 1`,
  `(M_d)_{1+r, 1+d} = 4`, `(M_/)₀₀ = (M_/)_{0, 1+r_in} = 1`, `(M_.)₀₀ = 1`, `v_. = e₀ + e_{1+r_out}`, all others 0;
  `r_in = 1` ($\mathcal T$, $\mathcal H$) or `0` ($R_H$, where `L` is `lft`), `r_out = 0` ($\mathcal T$) or `1` (the others).
* (i) Every rule is weakly oriented, none strictly, and `(M_s)₀₀ = 1` (`decide +kernel`).
* (ii) `Φ(can n) = 1 + 2^{ℓ(n)-1}[n ≡ r_out mod 3]` ($\mathcal T$, $\mathcal H$, `n ≥ 1`) and
  `Φ(canRH n) = 1 + 2^{ℓ(n)}[n ≡ 1 mod 3]` (`ℓ(n) = (Nat.digits 2 n).length`). By induction on the binary digits (appending a digit at the
  end of `binTail`), a row vector (1 on the slow path, a weight on the residue) is carried from the left (no large power is evaluated by `decide`).
  The values do not increase along $T$ (`n ≥ 2`) and $H$ (`HModel.HDom`).
* Corresponds to B1-B4 of the checking script `computations/check_mod3.py`.
-/
import CollatzProof.Arctic.RH.Defs
import CollatzProof.Arctic.HModel.Defs
import CollatzProof.Arctic.Canon

namespace Collatz.Arctic.NatExample

open Collatz.Arctic Matrix

/-! ## §1 Natural-number affine interpretations (the conventions of Section 2 of Paper II) -/

/-- A natural-number affine map `y ↦ M y + v` of dimension `d`. -/
structure NAff (d : ℕ) where
  M : Matrix (Fin d) (Fin d) ℕ
  v : Fin d → ℕ

/-- Application as a map: `F(y) = M y + v`. -/
def NAff.app {d : ℕ} (F : NAff d) (y : Fin d → ℕ) : Fin d → ℕ := F.M *ᵥ y + F.v

/-- The composition `F ∘ G`. -/
def NAff.comp {d : ℕ} (F G : NAff d) : NAff d := ⟨F.M * G.M, F.M *ᵥ G.v + F.v⟩

/-- The identity map. -/
def NAff.id (d : ℕ) : NAff d := ⟨1, 0⟩

/-- The interpretation of a string (`[s₁ ⋯ sₙ] = [s₁] ∘ ⋯ ∘ [sₙ]`; the empty string gives the identity). -/
def evN {d : ℕ} (I : Letter → NAff d) : Word → NAff d
  | [] => NAff.id d
  | s :: w => (I s).comp (evN I w)

/-- `evN` is the composition of the maps: `[s₁ ⋯ sₙ](y) = [s₁](⋯ [sₙ](y))`. -/
theorem evN_app {d : ℕ} (I : Letter → NAff d) (y : Fin d → ℕ) :
    ∀ w : Word, (evN I w).app y = w.foldr (fun s z => (I s).app z) y
  | [] => by simp [evN, NAff.app, NAff.id]
  | s :: w => by
    rw [List.foldr_cons, ← evN_app I y w]
    simp only [evN, NAff.comp, NAff.app, mulVec_add, mulVec_mulVec, add_assoc]

/-- Weak orientation: coefficientwise `M_ℓ ≥ M_r` and `v_ℓ ≥ v_r`. -/
def NWeak {d : ℕ} (I : Letter → NAff d) (ρ : Rule) : Prop :=
  (∀ i j, (evN I ρ.rhs).M i j ≤ (evN I ρ.lhs).M i j) ∧ ∀ i, (evN I ρ.rhs).v i ≤ (evN I ρ.lhs).v i

/-- Strict orientation ((2) of Yolcu–Aaronson–Heule): weak orientation, and the first component of `v` (index 0) is strictly larger. -/
def NStrict {d : ℕ} [NeZero d] (I : Letter → NAff d) (ρ : Rule) : Prop :=
  NWeak I ρ ∧ (evN I ρ.rhs).v 0 < (evN I ρ.lhs).v 0

/-- `Φ(w) = ([w](0))₁` (index 0). -/
def PhiN {d : ℕ} [NeZero d] (I : Letter → NAff d) (w : Word) : ℕ := (evN I w).app 0 0

instance {d : ℕ} (I : Letter → NAff d) (ρ : Rule) : Decidable (NWeak I ρ) :=
  @instDecidableAnd _ _
    (@Fintype.decidableForallFintype _ _
      (fun i => (inferInstance : Decidable (∀ j, (evN I ρ.rhs).M i j ≤ (evN I ρ.lhs).M i j))) _)
    inferInstance

/-- If the first components agree, the rule is not strictly oriented. -/
theorem not_strict_of_v0 {d : ℕ} [NeZero d] (I : Letter → NAff d) (ρ : Rule)
    (h : (evN I ρ.lhs).v 0 = (evN I ρ.rhs).v 0) : ¬ NStrict I ρ := fun hs => by
  have := hs.2; omega

/-! ## §2 The interpretation of dimension 4 -/

/-- The index of the residue `r mod 3` (`2 + r` in the paper, `1 + r` counting from 0). -/
def resIdx (r : ℕ) : Fin 4 := ⟨1 + r % 3, by omega⟩

/-- The matrix of the binary digit `b`: `(M_b)₀₀ = 1`, `(M_b)_{1+r, 1+(2r+b mod 3)} = 2`. -/
def matB (b : ℕ) : Matrix (Fin 4) (Fin 4) ℕ := Matrix.of fun i j =>
  if i = 0 then (if j = 0 then 1 else 0) else if j = resIdx (2 * (i.val - 1) + b) then 2 else 0

/-- The matrix of the ternary digit `d`: `(M_d)₀₀ = 1`, `(M_d)_{1+r, 1+d} = 4`. -/
def matD (d : ℕ) : Matrix (Fin 4) (Fin 4) ℕ := Matrix.of fun i j =>
  if i = 0 then (if j = 0 then 1 else 0) else if j = resIdx d then 4 else 0

/-- The matrix of the left end: `(M_/)₀₀ = (M_/)_{0, 1+r_in} = 1`. -/
def matL (rin : ℕ) : Matrix (Fin 4) (Fin 4) ℕ := Matrix.of fun i j =>
  if i = 0 ∧ (j = 0 ∨ j = resIdx rin) then 1 else 0

/-- The matrix of the right end: `(M_.)₀₀ = 1`. -/
def matR : Matrix (Fin 4) (Fin 4) ℕ := Matrix.of fun i j => if i = 0 ∧ j = 0 then 1 else 0

/-- The absolute part of the right end, `v_. = e₀ + e_{1+r_out}`. -/
def vecR (rout : ℕ) : Fin 4 → ℕ := fun i => if i = 0 ∨ i = resIdx rout then 1 else 0

/-- The interpretation (`v` is nonzero only for the right end). -/
def interp (rin rout : ℕ) : Letter → NAff 4
  | .f => ⟨matB 0, 0⟩
  | .t => ⟨matB 1, 0⟩
  | .d0 => ⟨matD 0, 0⟩
  | .d1 => ⟨matD 1, 0⟩
  | .d2 => ⟨matD 2, 0⟩
  | .lft => ⟨matL rin, 0⟩
  | .rgt => ⟨matR, vecR rout⟩

/-- $\mathcal T$: `r_in = 1`, `r_out = 0`. -/
def IT : Letter → NAff 4 := interp 1 0
/-- $\mathcal H$: `r_in = 1`, `r_out = 1`. -/
def IH : Letter → NAff 4 := interp 1 1
/-- $R_H$: `r_in = 0`, `r_out = 1`. -/
def IRH : Letter → NAff 4 := interp 0 1

theorem matB_zero : matB 0 = !![1, 0, 0, 0; 0, 2, 0, 0; 0, 0, 0, 2; 0, 0, 2, 0] := by decide
theorem matB_one : matB 1 = !![1, 0, 0, 0; 0, 0, 2, 0; 0, 2, 0, 0; 0, 0, 0, 2] := by decide
example : matD 2 = !![1, 0, 0, 0; 0, 0, 0, 4; 0, 0, 0, 4; 0, 0, 0, 4] := by decide
example : matL 1 = !![1, 0, 1, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] := by decide
example : vecR 1 = ![1, 0, 1, 0] := by decide

theorem interp_M00 (rin rout : ℕ) (s : Letter) : (interp rin rout s).M 0 0 = 1 := by
  cases s <;> simp [interp, matB, matD, matL, matR]

/-! ## §3 (i) Orientation -/

theorem weak_T : ∀ ρ ∈ rulesST, NWeak IT ρ := by decide +kernel
theorem v0_T : ∀ ρ ∈ rulesST, (evN IT ρ.lhs).v 0 = (evN IT ρ.rhs).v 0 := by decide +kernel
theorem weak_H : ∀ ρ ∈ HTPDB.rulesHT, NWeak IH ρ := by decide +kernel
theorem v0_H : ∀ ρ ∈ HTPDB.rulesHT, (evN IH ρ.lhs).v 0 = (evN IH ρ.rhs).v 0 := by decide +kernel
theorem weak_RH : ∀ ρ ∈ RH.rulesRH, NWeak IRH ρ := by decide +kernel
theorem v0_RH : ∀ ρ ∈ RH.rulesRH, (evN IRH ρ.lhs).v 0 = (evN IRH ρ.rhs).v 0 := by decide +kernel

/-! ## §4 Tools for computing values (carrying a row vector from the left) -/

/-- Multiplies the row vector `ρ` by the matrices of the letters of a string, from left to right. -/
def rowAfter {d : ℕ} (I : Letter → NAff d) (ρ : Fin d → ℕ) (w : Word) : Fin d → ℕ :=
  w.foldl (fun ρ s => ρ ᵥ* (I s).M) ρ

theorem rowAfter_cons {d : ℕ} (I : Letter → NAff d) (ρ : Fin d → ℕ) (s : Letter) (w : Word) :
    rowAfter I ρ (s :: w) = rowAfter I (ρ ᵥ* (I s).M) w := rfl

theorem rowAfter_append {d : ℕ} (I : Letter → NAff d) (ρ : Fin d → ℕ) (u w : Word) :
    rowAfter I ρ (u ++ w) = rowAfter I (rowAfter I ρ u) w := by
  simp [rowAfter, List.foldl_append]

/-- If a string `u` of letters with zero absolute parts is put in front, `ρ ⬝ v` becomes the row vector carried through `u`. -/
theorem dot_evN {d : ℕ} (I : Letter → NAff d) (w' : Word) :
    ∀ u : Word, (∀ s ∈ u, (I s).v = 0) → ∀ ρ : Fin d → ℕ,
      ρ ⬝ᵥ (evN I (u ++ w')).v = rowAfter I ρ u ⬝ᵥ (evN I w').v
  | [], _, _ => rfl
  | s :: u, hu, ρ => by
    have hs : (I s).v = 0 := hu s (by simp)
    change ρ ⬝ᵥ ((I s).M *ᵥ (evN I (u ++ w')).v + (I s).v) = _
    rw [hs, add_zero, dotProduct_mulVec, rowAfter_cons]
    exact dot_evN I w' u (fun s' hs' => hu s' (by simp [hs'])) _

theorem interp_v (rin rout : ℕ) (s : Letter) (hs : s ≠ Letter.rgt) : (interp rin rout s).v = 0 := by
  cases s <;> simp_all [interp]

/-- `Φ(u .) = (e₀ ⬝ M_u) ⬝ v_.` (when `u` contains no right end). -/
theorem phiN_append_rgt (rin rout : ℕ) (u : Word) (hu : ∀ s ∈ u, s ≠ Letter.rgt) :
    PhiN (interp rin rout) (u ++ [Letter.rgt]) =
      rowAfter (interp rin rout) (Pi.single 0 1) u ⬝ᵥ vecR rout := by
  have h0 : PhiN (interp rin rout) (u ++ [Letter.rgt]) =
      Pi.single 0 1 ⬝ᵥ (evN (interp rin rout) (u ++ [Letter.rgt])).v := by
    rw [single_dotProduct, one_mul]; simp [PhiN, NAff.app]
  have hr : (evN (interp rin rout) [Letter.rgt]).v = vecR rout := by
    simp [evN, NAff.comp, NAff.id, interp]
  rw [h0, dot_evN _ _ u (fun s hs => interp_v rin rout s (hu s hs)), hr]

theorem vecMul_matB_zero (ρ : Fin 4 → ℕ) : ρ ᵥ* matB 0 = ![ρ 0, 2 * ρ 1, 2 * ρ 3, 2 * ρ 2] := by
  rw [matB_zero]; funext j; fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_four] <;> ring

theorem vecMul_matB_one (ρ : Fin 4 → ℕ) : ρ ᵥ* matB 1 = ![ρ 0, 2 * ρ 2, 2 * ρ 1, 2 * ρ 3] := by
  rw [matB_one]; funext j; fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_four] <;> ring

/-- 1 on the slow path and `W` at the index of the residue `x mod 3`. -/
def resRow (W x : ℕ) : Fin 4 → ℕ :=
  if x % 3 = 0 then ![1, W, 0, 0] else if x % 3 = 1 then ![1, 0, W, 0] else ![1, 0, 0, W]

theorem resRow_mod (W x : ℕ) : resRow W (x % 3) = resRow W x := by simp [resRow]

/-- Reading one digit `b`: the residue becomes `2x + b`, and the weight doubles. -/
theorem resRow_vecMul_matB (W x b : ℕ) (hb : b < 2) :
    resRow W x ᵥ* matB b = resRow (2 * W) (2 * x + b) := by
  rw [← resRow_mod W x, ← resRow_mod (2 * W) (2 * x + b)]
  have h : (2 * x + b) % 3 = (2 * (x % 3) + b) % 3 := by omega
  rw [h]
  have hx : x % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize x % 3 = y at hx ⊢
  interval_cases y <;> interval_cases b <;> simp [resRow, vecMul_matB_zero, vecMul_matB_one]

theorem single_vecMul_matL (rin : ℕ) (hr : rin < 3) : Pi.single 0 1 ᵥ* matL rin = resRow 1 rin := by
  interval_cases rin <;> decide

theorem resRow_dot_vecR (V x rout : ℕ) (hr : rout < 3) :
    resRow V x ⬝ᵥ vecR rout = 1 + if x % 3 = rout then V else 0 := by
  rw [← resRow_mod V x]
  have hx : x % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize x % 3 = y at hx ⊢
  interval_cases y <;> interval_cases rout <;> simp [resRow, vecR, dotProduct, Fin.sum_univ_four, resIdx]

theorem binTail_ne_rgt (n : ℕ) : ∀ s ∈ binTail n, s ≠ Letter.rgt := by
  intro s hs
  unfold binTail at hs
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hs
  split_ifs <;> simp

theorem len_binTail (n : ℕ) : (binTail n).length = (Nat.digits 2 n).length - 1 := by
  simp [binTail]

theorem digits_len_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ (Nat.digits 2 n).length :=
  List.length_pos_iff.mpr (digits_two_ne_nil n hn)

/-- Reading the binary digits below the leading one: starting from the residue 1 one arrives at `n mod 3`, and the weight is multiplied by `2^{ℓ(n)-1}`. -/
theorem rowAfter_binTail (rin rout : ℕ) :
    ∀ n, 1 ≤ n → ∀ W, rowAfter (interp rin rout) (resRow W 1) (binTail n) =
      resRow (W * 2 ^ (binTail n).length) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn W
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      simp [binTail_one, rowAfter]
    · have hy : 1 ≤ n / 2 := by omega
      have hb : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have hn' : n = 2 * (n / 2) + n % 2 := by omega
      rw [hn', binTail_two_mul_add _ _ hy hb, rowAfter_append, ih (n / 2) (by omega) hy W]
      have hM : (interp rin rout (bitL (n % 2))).M = matB (n % 2) := by
        interval_cases (n % 2) <;> rfl
      simp only [rowAfter, List.foldl_cons, List.foldl_nil, hM, resRow_vecMul_matB _ _ _ hb,
        List.length_append, List.length_singleton, pow_succ]
      congr 1; ring

/-! ## §5 (ii) The formula for the values -/

/-- The form for $\mathcal T$ and $\mathcal H$ (`r_in = 1`): `Φ(can n) = 1 + 2^{ℓ(n)-1}[n ≡ r_out mod 3]`. -/
theorem phi_can (rout : ℕ) (hr : rout < 3) (n : ℕ) (hn : 1 ≤ n) :
    PhiN (interp 1 rout) (can n) = 1 + if n % 3 = rout then 2 ^ ((Nat.digits 2 n).length - 1) else 0 := by
  have hc : can n = (Letter.lft :: binTail n) ++ [Letter.rgt] := by simp [can]
  have hu : ∀ s ∈ Letter.lft :: binTail n, s ≠ Letter.rgt := by
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · decide
    · exact binTail_ne_rgt n s hs
  rw [hc, phiN_append_rgt _ _ _ hu, rowAfter_cons]
  change rowAfter _ (Pi.single 0 1 ᵥ* matL 1) _ ⬝ᵥ _ = _
  rw [single_vecMul_matL 1 (by norm_num), rowAfter_binTail _ _ n hn, resRow_dot_vecR _ _ _ hr,
    len_binTail, one_mul]

theorem phi_can_T (n : ℕ) (hn : 1 ≤ n) :
    PhiN IT (can n) = 1 + if n % 3 = 0 then 2 ^ ((Nat.digits 2 n).length - 1) else 0 :=
  phi_can 0 (by norm_num) n hn

theorem phi_can_H (n : ℕ) (hn : 1 ≤ n) :
    PhiN IH (can n) = 1 + if n % 3 = 1 then 2 ^ ((Nat.digits 2 n).length - 1) else 0 :=
  phi_can 1 (by norm_num) n hn

/-- $R_H$ (`r_in = 0`; the leading one is read as the letter `t`): `Φ(canRH n) = 1 + 2^{ℓ(n)}[n ≡ 1 mod 3]`. -/
theorem phi_canRH (n : ℕ) (hn : 1 ≤ n) :
    PhiN IRH (RH.canRH n) = 1 + if n % 3 = 1 then 2 ^ (Nat.digits 2 n).length else 0 := by
  have hc : RH.canRH n = (Letter.lft :: Letter.t :: binTail n) ++ [Letter.rgt] := by simp [RH.canRH]
  have hu : ∀ s ∈ Letter.lft :: Letter.t :: binTail n, s ≠ Letter.rgt := by
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · decide
    rcases List.mem_cons.mp hs with rfl | hs
    · decide
    · exact binTail_ne_rgt n s hs
  unfold IRH
  rw [hc, phiN_append_rgt _ _ _ hu, rowAfter_cons, rowAfter_cons]
  change rowAfter _ (Pi.single 0 1 ᵥ* matL 0 ᵥ* matB 1) _ ⬝ᵥ _ = _
  rw [single_vecMul_matL 0 (by norm_num), resRow_vecMul_matB 1 0 1 (by norm_num)]
  rw [show 2 * 0 + 1 = 1 from rfl, rowAfter_binTail _ _ n hn, resRow_dot_vecR _ _ _ (by norm_num),
    len_binTail]
  have h1 := digits_len_pos n hn
  rw [← pow_succ', Nat.sub_add_cancel h1]

/-! ## §6 (ii) The values do not increase along $T$ and $H$ -/

theorem phi_can_ge_one (rout : ℕ) (hr : rout < 3) (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ PhiN (interp 1 rout) (can n) := by
  rw [phi_can rout hr n hn]; omega

/-- $\mathcal T$: `Φ(can (T n)) ≤ Φ(can n)` for `n ≥ 2` (`3 ∣ T(n)` only if `n` is even and `3 ∣ n`, and then
`ℓ(T(n)) = ℓ(n) - 1`). -/
theorem phi_T_noninc (n : ℕ) (hn : 2 ≤ n) : PhiN IT (can (T n)) ≤ PhiN IT (can n) := by
  rcases Nat.even_or_odd' n with ⟨y, rfl | rfl⟩
  · have hT : T (2 * y) = y := by simp [T]
    have hd : (Nat.digits 2 (2 * y)).length = (Nat.digits 2 y).length + 1 := by
      have := digits_two_mul_add y 0 (by omega) (by norm_num)
      rw [add_zero] at this; rw [this, List.length_cons]
    rw [hT, phi_can_T y (by omega), phi_can_T (2 * y) (by omega), hd]
    have hpow : 2 ^ ((Nat.digits 2 y).length - 1) ≤ 2 ^ ((Nat.digits 2 y).length + 1 - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    split_ifs <;> omega
  · have hT : T (2 * y + 1) = 3 * y + 2 := by simp [T]; omega
    have h3 : (3 * y + 2) % 3 ≠ 0 := by omega
    have h1 := phi_can_ge_one 0 (by norm_num) (2 * y + 1) (by omega)
    rw [hT, phi_can_T (3 * y + 2) (by omega)]
    simp only [h3, ↓reduceIte, add_zero]
    exact h1

/-- At the points of the domain, `H(n) ≢ 1 (mod 3)` and `H(n) ≥ 1`. -/
theorem Hmap_mod3 (n : ℕ) (hn : HModel.HDom n) : HModel.Hmap n % 3 ≠ 1 ∧ 1 ≤ HModel.Hmap n := by
  obtain ⟨h8, h⟩ := hn
  unfold HModel.Hmap
  split_ifs <;> omega

theorem phi_H_Hmap (n : ℕ) (hn : HModel.HDom n) : PhiN IH (can (HModel.Hmap n)) = 1 := by
  obtain ⟨h1, h2⟩ := Hmap_mod3 n hn
  rw [phi_can_H _ h2]
  simp only [h1, ↓reduceIte, add_zero]

/-- $\mathcal H$: `Φ(can (H n)) ≤ Φ(can n)` at the points of the domain. -/
theorem phi_H_noninc (n : ℕ) (hn : HModel.HDom n) : PhiN IH (can (HModel.Hmap n)) ≤ PhiN IH (can n) := by
  rw [phi_H_Hmap n hn]; exact phi_can_ge_one 1 (by norm_num) n (by have := hn.1; omega)

theorem phi_RH_Hmap (n : ℕ) (hn : HModel.HDom n) : PhiN IRH (RH.canRH (HModel.Hmap n)) = 1 := by
  obtain ⟨h1, h2⟩ := Hmap_mod3 n hn
  rw [phi_canRH _ h2]
  simp only [h1, ↓reduceIte, add_zero]

/-- $R_H$: `Φ(canRH (H n)) ≤ Φ(canRH n)` at the points of the domain. -/
theorem phi_RH_noninc (n : ℕ) (hn : HModel.HDom n) :
    PhiN IRH (RH.canRH (HModel.Hmap n)) ≤ PhiN IRH (RH.canRH n) := by
  rw [phi_RH_Hmap n hn, phi_canRH n (by have := hn.1; omega)]; omega

end Collatz.Arctic.NatExample
