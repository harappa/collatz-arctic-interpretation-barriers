/-
# 𝒯: the value embedding (Lemma 10.5 of the paper) and the equivalence of the value-level cores

This file formalizes the value embedding (Lemma 10.5 of the paper), which was proposed in the internal independent review
(as "Lemma E" of the reviewer's report).

* **The value-level core for general families** `GenValueCore` (§1): for non-negative integer matrices `N_s` (7 letters) on a finite type of indices `ι` and indices `a, z`,
  if `N_ℓ ≥ N_r` entrywise for all 11 rules (`GWeak`), then for every rule `ρ` and every `K` there are `n ≥ K` and a segment
  `n → T^m n` of an orbit (all points at least 2) on which the number of uses of `ρ` exceeds `(N_{can n})_{az}`. The form of the conclusion is
  the same as in `NatValueCore`. The form was chosen so that transposition (Lemma 10.4 of the paper: `N'_s := N_s^T`, `Φ^rev(n) = (N'_{can n})_{d0}`, and the weak
  orientation of 𝒯^rev is `N'_ℓ ≥ N'_r` for the 11 rules of 𝒯) fits directly (any type of indices, no structural assumption, the value is a single entry).
* **Transfer** (§2): a family with a sink index `none` (the row of `none` is `e_none^T`) becomes, via a bijection of coordinates `e : Fin d ≃ κ`,
  a natural-number matrix interpretation `ofHom e Nt` (`homN_ofHom`). Values, weak orientation and monotonicity are carried over
  (`phiN_ofHom`, `nweak_ofHom_iff`, `nmono_ofHom_iff`).
* **Lemma 10.5** (§3): the family with a source `a* = some none` and a sink `s* = none` added,
  `Ñ_x = \begin{pmatrix} 1 & γ_x & 0 \\ 0 & N_x & β_x \\ 0 & 0 & 1 \end{pmatrix}` (in the order `a*`, `ι`, `s*`),
  `γ_/ = e_a^T N_/`, `β_. = N_. e_z`, and `γ = β = 0` for the other letters (`embFam`).
  - `s*` is the homogeneous index (its row is `e_{s*}^T`, `embFam_sink`), and `a*` is the index of monotonicity (its diagonal entry is 1).
  - All 11 rules are weakly oriented (`embFam_gweak`). Only rules 8 to 10 contain `/`, only rules 0 and 1 contain `.`, and
    no rule contains both (`rules_lft_shape`, `rules_rgt_shape`, `rules_not_both`, by `decide` from the list of rules).
  - For every `n` the value equals `(N_{can n})_{az}` (`embFam_can`).
  - The embedding does not preserve strict orientation (the example of `NonVacuityW1.lean`).
* **Equivalence of the value-level cores** (§4): `NatValueCore → GenValueCore` (Lemma 10.5), `GenValueCore → NatValueCore'` (homogeneous matrices,
  `a = some 0`, `z = none`), and `NatValueCore' → NatValueCore` (existing). The three are equivalent (`genValueCore_iff`,
  `natValueCore_iff_natValueCore'`). They are also equivalent to the form `NatValueCoreSrc` restricted to interpretations in which the diagonal entry at the index of monotonicity is exactly 1
  and that index is a source (no edge enters it from other indices) (`natValueCoreSrc_iff`; the image of the embedding has this form).
* **Transposition** (§5): the products of words of the transposed family are the transposes of the products of the reversed words (`NW_transpose`). The transposed family weakly orients `ρ`
  if and only if the original family weakly orients the reversed rule `ruleRev ρ` (`gweak_transpose_iff`). `Φ^rev(n)` is the `(none, some 0)` entry of the family of transposed
  homogeneous matrices (`phiN_rev_eq_transpose`). So interpretations of 𝒯^rev fit, after transposition, directly into the premise of `GenValueCore`
  (the reversed statements and the reversed bridge (Lemma 13.1 of the paper) are in later files).
-/
import CollatzProof.Arctic.Nat.ValueAuto

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Matrix Letter

set_option linter.unusedSectionVars false

/-! ## §1 The value-level core for general families -/

/-- **The value-level core for general families**: for a family `N` of non-negative integer matrices on a finite type of indices `ι` (no structural assumption) and indices `a, z`
that weakly orients all 11 rules of 𝒯 entrywise (`N_ℓ ≥ N_r`), for every rule `ρ` and every `K` there is a segment
`n → T^m n` of a `T`-orbit (all points of the segment at least 2) on which the number of uses of `ρ` exceeds the value `(N_{can n})_{az}`. -/
def GenValueCore : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : Letter → Matrix ι ι ℕ) (a z : ι),
    (∀ ρ ∈ rulesST, GWeak N ρ) →
    ∀ ρ ∈ rulesST, ∀ K : ℕ, ∃ n, K ≤ n ∧ ∃ m : ℕ,
      (∀ i < m, 2 ≤ T^[i] n) ∧ NW N (can n) a z < usesOrbit ρ n m

/-! ## §2 From families with a sink index to natural-number matrix interpretations -/

section Transfer

variable {d : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Renaming indices: products of words are carried over by the renaming. -/
theorem NW_submatrix {ι' ι : Type*} [Fintype ι'] [DecidableEq ι'] [Fintype ι] [DecidableEq ι]
    (Nt : Letter → Matrix ι ι ℕ) (f : ι' ≃ ι) :
    ∀ w : Word, NW (fun x => (Nt x).submatrix f f) w = (NW Nt w).submatrix f f
  | [] => by simp [Matrix.submatrix_one_equiv]
  | x :: w => by rw [NW_cons, NW_cons, NW_submatrix Nt f w, Matrix.submatrix_mul_equiv]

/-- The natural-number matrix interpretation built from a family `Nt` with a sink index `none` (type of indices `Option κ`) and coordinates `e : Fin d ≃ κ`
(`M_x :=` the `κ × κ` part of `Nt_x`, `v_x :=` the column `none` of `Nt_x`). -/
def ofHom (e : Fin d ≃ κ) (Nt : Letter → Matrix (Option κ) (Option κ) ℕ) : Letter → NAff d :=
  fun x => ⟨fun i j => Nt x (some (e i)) (some (e j)), fun i => Nt x (some (e i)) none⟩

theorem homN_ofHom (e : Fin d ≃ κ) (Nt : Letter → Matrix (Option κ) (Option κ) ℕ)
    (hsink : ∀ x q, Nt x none q = if q = none then 1 else 0) (x : Letter) :
    homN (ofHom e Nt x) = (Nt x).submatrix (Equiv.optionCongr e) (Equiv.optionCongr e) := by
  ext p q
  cases p <;> cases q <;> simp [ofHom, hsink]

theorem homFam_ofHom (e : Fin d ≃ κ) (Nt : Letter → Matrix (Option κ) (Option κ) ℕ)
    (hsink : ∀ x q, Nt x none q = if q = none then 1 else 0) :
    homFam (ofHom e Nt) = fun x => (Nt x).submatrix (Equiv.optionCongr e) (Equiv.optionCongr e) :=
  funext fun x => homN_ofHom e Nt hsink x

theorem nw_ofHom (e : Fin d ≃ κ) (Nt : Letter → Matrix (Option κ) (Option κ) ℕ)
    (hsink : ∀ x q, Nt x none q = if q = none then 1 else 0) (w : Word) :
    NW (homFam (ofHom e Nt)) w = (NW Nt w).submatrix (Equiv.optionCongr e) (Equiv.optionCongr e) := by
  rw [homFam_ofHom e Nt hsink, NW_submatrix]

/-- Values are carried over: `Φ(w) = (Nt_w)_{(some (e 0)), none}`. -/
theorem phiN_ofHom [NeZero d] (e : Fin d ≃ κ) (Nt : Letter → Matrix (Option κ) (Option κ) ℕ)
    (hsink : ∀ x q, Nt x none q = if q = none then 1 else 0) (w : Word) :
    PhiN (ofHom e Nt) w = NW Nt w (some (e 0)) none := by
  rw [phiN_eq_nw, nw_ofHom e Nt hsink]
  simp

/-- Weak orientation is carried over. -/
theorem nweak_ofHom_iff (e : Fin d ≃ κ) (Nt : Letter → Matrix (Option κ) (Option κ) ℕ)
    (hsink : ∀ x q, Nt x none q = if q = none then 1 else 0) (ρ : Rule) :
    NWeak (ofHom e Nt) ρ ↔ GWeak Nt ρ := by
  rw [nweak_iff_gweak]
  unfold GWeak
  rw [nw_ofHom e Nt hsink, nw_ofHom e Nt hsink]
  simp only [Matrix.submatrix_apply]
  constructor
  · intro h p q
    have := h ((Equiv.optionCongr e).symm p) ((Equiv.optionCongr e).symm q)
    simpa using this
  · intro h p q
    exact h _ _

/-- Monotonicity: the diagonal entry at the index 0 (coordinate `e 0`). -/
theorem nmono_ofHom_iff [NeZero d] (e : Fin d ≃ κ) (Nt : Letter → Matrix (Option κ) (Option κ) ℕ) :
    NMono (ofHom e Nt) ↔ ∀ x, 1 ≤ Nt x (some (e 0)) (some (e 0)) := Iff.rfl

end Transfer

/-! ## §3 Lemma 10.5: the family with a source and a sink added -/

section Embed

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The family of Lemma 10.5** (type of indices `Option (Option ι)`: `none` is the sink `s*`, `some none` the source `a*`, and `some (some i)`
the index `i`). `Ñ_x = \begin{pmatrix} 1 & γ_x & 0 \\ 0 & N_x & β_x \\ 0 & 0 & 1 \end{pmatrix}`, `γ_/ = e_a^T N_/`,
`β_. = N_. e_z`, and `γ = β = 0` for the other letters. -/
def embFam (N : Letter → Matrix ι ι ℕ) (a z : ι) (x : Letter) :
    Matrix (Option (Option ι)) (Option (Option ι)) ℕ := fun p q =>
  match p, q with
  | none, none => 1
  | none, some _ => 0
  | some none, none => 0
  | some none, some none => 1
  | some none, some (some j) => if x = lft then N lft a j else 0
  | some (some i), none => if x = rgt then N rgt i z else 0
  | some (some _), some none => 0
  | some (some i), some (some j) => N x i j

variable (N : Letter → Matrix ι ι ℕ) (a z : ι)

local notation "Ñ" => embFam N a z

@[simp] theorem emb_nn (x : Letter) : Ñ x none none = 1 := rfl
@[simp] theorem emb_ns (x : Letter) (q : Option ι) : Ñ x none (some q) = 0 := rfl
@[simp] theorem emb_an (x : Letter) : Ñ x (some none) none = 0 := rfl
@[simp] theorem emb_aa (x : Letter) : Ñ x (some none) (some none) = 1 := rfl
@[simp] theorem emb_ai (x : Letter) (j : ι) :
    Ñ x (some none) (some (some j)) = if x = lft then N lft a j else 0 := rfl
@[simp] theorem emb_in (x : Letter) (i : ι) : Ñ x (some (some i)) none = if x = rgt then N rgt i z else 0 := rfl
@[simp] theorem emb_ia (x : Letter) (i : ι) : Ñ x (some (some i)) (some none) = 0 := rfl
@[simp] theorem emb_ii (x : Letter) (i j : ι) : Ñ x (some (some i)) (some (some j)) = N x i j := rfl

/-- The sink: the row of `s*` is `e_{s*}^T`. -/
theorem embFam_sink (x : Letter) (q : Option (Option ι)) : Ñ x none q = if q = none then 1 else 0 := by
  rcases q with _ | q <;> rfl

/-- Expanding one step of a product (splitting the sum over the type of indices `Option (Option ι)` into three). -/
theorem nw_emb_cons (x : Letter) (w : Word) (p q : Option (Option ι)) :
    NW Ñ (x :: w) p q = Ñ x p none * NW Ñ w none q + Ñ x p (some none) * NW Ñ w (some none) q +
      ∑ k, Ñ x p (some (some k)) * NW Ñ w (some (some k)) q := by
  rw [NW_cons, Matrix.mul_apply, Fintype.sum_option, Fintype.sum_option, add_assoc]

/-- (i) The row of the sink. -/
theorem nw_emb_none (w : Word) (q : Option (Option ι)) : NW Ñ w none q = if q = none then 1 else 0 := by
  induction w with
  | nil => rcases q with _ | _ | _ <;> simp
  | cons x w ih => rw [nw_emb_cons, ih]; simp

/-- (iii) The entries from an index `i` to the source are 0. -/
theorem nw_emb_ia (w : Word) (i : ι) : NW Ñ w (some (some i)) (some none) = 0 := by
  induction w generalizing i with
  | nil => simp
  | cons x w ih => rw [nw_emb_cons, nw_emb_none]; simp [ih]

/-- (ii) The diagonal entry of the source is 1. -/
theorem nw_emb_aa (w : Word) : NW Ñ w (some none) (some none) = 1 := by
  induction w with
  | nil => simp
  | cons x w ih => rw [nw_emb_cons, nw_emb_none, ih]; simp [nw_emb_ia]

/-- (iv) The `ι × ι` part is the product of the original family. -/
theorem nw_emb_ii (w : Word) (i j : ι) : NW Ñ w (some (some i)) (some (some j)) = NW N w i j := by
  induction w generalizing i with
  | nil => simp [Matrix.one_apply]
  | cons x w ih =>
    rw [nw_emb_cons, nw_emb_none, NW_cons, Matrix.mul_apply]
    simp [ih]

/-- (v) For words without `/`, the entries from the source to an index `j` are 0. -/
theorem nw_emb_ai_of_not_mem (w : Word) (hw : lft ∉ w) (j : ι) : NW Ñ w (some none) (some (some j)) = 0 := by
  induction w with
  | nil => simp
  | cons x w ih =>
    have hx : x ≠ lft := fun h => hw (h ▸ List.mem_cons_self)
    have hw' : lft ∉ w := fun h => hw (List.mem_cons_of_mem _ h)
    rw [nw_emb_cons, nw_emb_none, ih hw']
    simp [hx]

/-- (vi) For words without `/`, the entry from the source to the sink is 0. -/
theorem nw_emb_an_of_not_lft (w : Word) (hw : lft ∉ w) : NW Ñ w (some none) none = 0 := by
  induction w with
  | nil => simp
  | cons x w ih =>
    have hx : x ≠ lft := fun h => hw (h ▸ List.mem_cons_self)
    have hw' : lft ∉ w := fun h => hw (List.mem_cons_of_mem _ h)
    rw [nw_emb_cons, ih hw']
    simp [hx]

/-- (vii) For words without `.`, the entries from an index `i` to the sink are 0. -/
theorem nw_emb_in_of_not_mem (w : Word) (hw : rgt ∉ w) (i : ι) : NW Ñ w (some (some i)) none = 0 := by
  induction w generalizing i with
  | nil => simp
  | cons x w ih =>
    have hx : x ≠ rgt := fun h => hw (h ▸ List.mem_cons_self)
    have hw' : rgt ∉ w := fun h => hw (List.mem_cons_of_mem _ h)
    rw [nw_emb_cons, nw_emb_none]
    simp [hx, ih hw']

/-- (viii) For words without `.`, the entry from the source to the sink is 0. -/
theorem nw_emb_an_of_not_rgt (w : Word) (hw : rgt ∉ w) : NW Ñ w (some none) none = 0 := by
  induction w with
  | nil => simp
  | cons x w ih =>
    have hw' : rgt ∉ w := fun h => hw (List.mem_cons_of_mem _ h)
    rw [nw_emb_cons, ih hw']
    simp [nw_emb_in_of_not_mem N a z w hw']

/-- (ix) For `/ w` (`w` without `/`), the entry from the source to an index `j` is `(N_{/ w})_{aj}`. -/
theorem nw_emb_ai_lft (w : Word) (hw : lft ∉ w) (j : ι) :
    NW Ñ (lft :: w) (some none) (some (some j)) = NW N (lft :: w) a j := by
  rw [nw_emb_cons, nw_emb_none, nw_emb_ai_of_not_mem N a z w hw, NW_cons, Matrix.mul_apply]
  simp [nw_emb_ii]

/-- (x) For `w .` (`w` without `.`), the entry from an index `i` to the sink is `(N_{w .})_{iz}`. -/
theorem nw_emb_in_rgt (w : Word) (hw : rgt ∉ w) (i : ι) :
    NW Ñ (w ++ [rgt]) (some (some i)) none = NW N (w ++ [rgt]) i z := by
  induction w generalizing i with
  | nil =>
    rw [List.nil_append, nw_emb_cons, nw_emb_none, NW_singleton]
    simp
  | cons x w ih =>
    have hx : x ≠ rgt := fun h => hw (h ▸ List.mem_cons_self)
    have hw' : rgt ∉ w := fun h => hw (List.mem_cons_of_mem _ h)
    rw [List.cons_append, nw_emb_cons, nw_emb_none, NW_cons, Matrix.mul_apply]
    simp [hx, ih hw']

/-- (xi) For `/ w` (`w` without `/`), the entry from the source to the sink is `Σ_k (N_/)_{ak} (Ñ_w)_{k s*}`. -/
theorem nw_emb_an_lft (w : Word) (hw : lft ∉ w) :
    NW Ñ (lft :: w) (some none) none = ∑ k, N lft a k * NW Ñ w (some (some k)) none := by
  rw [nw_emb_cons, nw_emb_an_of_not_lft N a z w hw]
  simp

/-- **Lemma 10.5 (values)**: `(Ñ_{can n})_{a* s*} = (N_{can n})_{az}` for every `n`. -/
theorem embFam_can (n : ℕ) : NW Ñ (can n) (some none) none = NW N (can n) a z := by
  have hl : lft ∉ (binWord n).map bitLetter ++ [rgt] := by
    simp only [List.mem_append, List.mem_map, List.mem_singleton, not_or, not_exists, not_and]
    refine ⟨fun b _ h => ?_, by decide⟩
    unfold bitLetter at h; split_ifs at h
  have hr : rgt ∉ (binWord n).map bitLetter := by
    simp only [List.mem_map, not_exists, not_and]
    intro b _ h; unfold bitLetter at h; split_ifs at h
  rw [can_eq, nw_emb_an_lft N a z _ hl]
  simp only [nw_emb_in_rgt N a z _ hr, NW_cons, Matrix.mul_apply]

/-! ### The shapes of the rules (from the list of rules) -/

/-- Only rules 8 to 10 contain `/`; both their sides begin with `/` and contain no other `/`. -/
theorem rules_lft_shape : ∀ ρ ∈ rulesST, (lft ∉ ρ.lhs ∧ lft ∉ ρ.rhs) ∨
    (ρ.lhs.head? = some lft ∧ ρ.rhs.head? = some lft ∧ lft ∉ ρ.lhs.tail ∧ lft ∉ ρ.rhs.tail) := by
  decide

/-- Only rules 0 and 1 contain `.`; both their sides end with `.` and contain no other `.`. -/
theorem rules_rgt_shape : ∀ ρ ∈ rulesST, (rgt ∉ ρ.lhs ∧ rgt ∉ ρ.rhs) ∨
    (ρ.lhs.getLast? = some rgt ∧ ρ.rhs.getLast? = some rgt ∧ rgt ∉ ρ.lhs.dropLast ∧ rgt ∉ ρ.rhs.dropLast) := by
  decide

/-- No rule contains both `/` and `.`. -/
theorem rules_not_both : ∀ ρ ∈ rulesST, (lft ∉ ρ.lhs ∧ lft ∉ ρ.rhs) ∨ (rgt ∉ ρ.lhs ∧ rgt ∉ ρ.rhs) := by
  decide

theorem nw_emb_ai_head (w : Word) (h : w.head? = some lft) (h' : lft ∉ w.tail) (j : ι) :
    NW Ñ w (some none) (some (some j)) = NW N w a j := by
  obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.1 h
  exact nw_emb_ai_lft N a z t h' j

theorem nw_emb_in_last (w : Word) (h : w.getLast? = some rgt) (h' : rgt ∉ w.dropLast) (i : ι) :
    NW Ñ w (some (some i)) none = NW N w i z := by
  have hw := List.dropLast_append_getLast? rgt h
  rw [← hw]
  exact nw_emb_in_rgt N a z _ h' i

/-- **Lemma 10.5 (weak orientation)**: if the original family weakly orients all 11 rules, so does `Ñ`. -/
theorem embFam_gweak (hweak : ∀ ρ ∈ rulesST, GWeak N ρ) : ∀ ρ ∈ rulesST, GWeak Ñ ρ := by
  intro ρ hρ p q
  have hN := hweak ρ hρ
  rcases p with _ | _ | i
  · rw [nw_emb_none, nw_emb_none]
  · rcases q with _ | _ | j
    · rcases rules_not_both ρ hρ with ⟨_, hr⟩ | ⟨_, hr⟩
      · rw [nw_emb_an_of_not_lft N a z _ hr]; exact Nat.zero_le _
      · rw [nw_emb_an_of_not_rgt N a z _ hr]; exact Nat.zero_le _
    · rw [nw_emb_aa, nw_emb_aa]
    · rcases rules_lft_shape ρ hρ with ⟨hl, hr⟩ | ⟨hl, hr, hl', hr'⟩
      · rw [nw_emb_ai_of_not_mem N a z _ hl, nw_emb_ai_of_not_mem N a z _ hr]
      · rw [nw_emb_ai_head N a z _ hl hl', nw_emb_ai_head N a z _ hr hr']
        exact hN a j
  · rcases q with _ | _ | j
    · rcases rules_rgt_shape ρ hρ with ⟨hl, hr⟩ | ⟨hl, hr, hl', hr'⟩
      · rw [nw_emb_in_of_not_mem N a z _ hl, nw_emb_in_of_not_mem N a z _ hr]
      · rw [nw_emb_in_last N a z _ hl hl', nw_emb_in_last N a z _ hr hr']
        exact hN i z
    · rw [nw_emb_ia, nw_emb_ia]
    · rw [nw_emb_ii, nw_emb_ii]; exact hN i j

end Embed

/-! ## §4 Equivalence of the value-level cores -/

/-- Coordinates: `Fin (|ι| + 1) ≃ Option ι`; the index 0 is `none` (the source `a*` in the embedding). -/
noncomputable def embEquiv (ι : Type*) [Fintype ι] : Fin (Fintype.card ι + 1) ≃ Option ι :=
  (finSuccEquiv _).trans (Equiv.optionCongr (Fintype.equivFin ι).symm)

@[simp] theorem embEquiv_zero (ι : Type*) [Fintype ι] : embEquiv ι 0 = none := by
  simp [embEquiv]

/-- The natural-number matrix interpretation of Lemma 10.5 (dimension `|ι| + 1`). -/
noncomputable def embInterp {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Letter → Matrix ι ι ℕ) (a z : ι) :
    Letter → NAff (Fintype.card ι + 1) :=
  ofHom (embEquiv ι) (embFam N a z)

section EmbInterp

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Letter → Matrix ι ι ℕ) (a z : ι)

/-- Monotone: the diagonal entry at the index 0 is exactly 1. -/
theorem embInterp_M00 (s : Letter) : (embInterp N a z s).M 0 0 = 1 := by
  show embFam N a z s (some (embEquiv ι 0)) (some (embEquiv ι 0)) = 1
  rw [embEquiv_zero]; rfl

theorem embInterp_mono : NMono (embInterp N a z) := fun s => (embInterp_M00 N a z s).ge

/-- Source: no edge enters the index 0 from other indices (column 0 of `M` is `e_0`). -/
theorem embInterp_col0 (s : Letter) (i : Fin (Fintype.card ι + 1)) (hi : i ≠ 0) :
    (embInterp N a z s).M i 0 = 0 := by
  show embFam N a z s (some (embEquiv ι i)) (some (embEquiv ι 0)) = 0
  rw [embEquiv_zero]
  have : embEquiv ι i ≠ none := by
    rw [← embEquiv_zero ι]; exact fun h => hi ((embEquiv ι).injective h)
  obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 this
  rw [hk]; rfl

theorem embInterp_weak (hweak : ∀ ρ ∈ rulesST, GWeak N ρ) : ∀ ρ ∈ rulesST, NWeak (embInterp N a z) ρ :=
  fun ρ hρ => (nweak_ofHom_iff _ _ (embFam_sink N a z) ρ).2 (embFam_gweak N a z hweak ρ hρ)

theorem embInterp_phi (n : ℕ) : PhiN (embInterp N a z) (can n) = NW N (can n) a z := by
  rw [embInterp, phiN_ofHom _ _ (embFam_sink N a z), embEquiv_zero, embFam_can]

/-- **The embedding does not preserve strict orientation**: the embedding strictly orients no rule (every rule misses `/` or `.`,
so the `(a*, s*)` entries of both sides are 0). So the frozen statement `NatBarrierST` does not give the barrier for general families; it follows from the value-level core
(a remark of the internal review). -/
theorem embInterp_not_strict : ∀ ρ ∈ rulesST, ¬ NStrict (embInterp N a z) ρ := by
  intro ρ hρ hs
  have hlhs : (evN (embInterp N a z) ρ.lhs).v 0 = 0 := by
    rw [← phiN_eq, embInterp, phiN_ofHom _ _ (embFam_sink N a z), embEquiv_zero]
    rcases rules_not_both ρ hρ with ⟨hl, _⟩ | ⟨hl, _⟩
    · exact nw_emb_an_of_not_lft N a z _ hl
    · exact nw_emb_an_of_not_rgt N a z _ hl
  have := hs.2
  omega

end EmbInterp

/-- **From Lemma 10.5**: the value-level core for general families from the value-level core in the monotone natural-number form. -/
theorem genValueCore_of_natValueCore (h : NatValueCore) : GenValueCore := by
  intro ι _ _ N a z hweak ρ hρ K
  obtain ⟨n, hn, m, horb, hlt⟩ :=
    h (Fintype.card ι + 1) (embInterp N a z) (embInterp_mono N a z) (embInterp_weak N a z hweak) ρ hρ K
  exact ⟨n, hn, m, horb, by rwa [embInterp_phi] at hlt⟩

/-- From the value-level core for general families to the value-level core in the natural-number form without monotonicity (homogeneous matrices, `a = some 0`, `z = none`). -/
theorem natValueCore'_of_genValueCore (h : GenValueCore) : NatValueCore' := by
  intro d _ I hweak ρ hρ K
  obtain ⟨n, hn, m, horb, hlt⟩ :=
    h (Option (Fin d)) (homFam I) (some 0) none (fun σ hσ => gweak_of_nweak (hweak σ hσ)) ρ hρ K
  exact ⟨n, hn, m, horb, by rwa [phiN_eq_nw]⟩

/-- The value-level cores in the monotone form and in the form without monotonicity are equivalent. -/
theorem natValueCore_iff_natValueCore' : NatValueCore ↔ NatValueCore' :=
  ⟨fun h => natValueCore'_of_genValueCore (genValueCore_of_natValueCore h), natValueCore_of_core'⟩

/-- The value-level core for general families is equivalent to the value-level core in the monotone natural-number form. -/
theorem genValueCore_iff : GenValueCore ↔ NatValueCore :=
  ⟨fun h => natValueCore_of_core' (natValueCore'_of_genValueCore h), genValueCore_of_natValueCore⟩

/-- The value-level core restricted to the form in which the diagonal entry at the index of monotonicity is exactly 1 and no edge enters the index 0 from other indices (a source).
The image of Lemma 10.5 has this form. -/
def NatValueCoreSrc : Prop :=
  ∀ (d : ℕ) [NeZero d] (I : Letter → NAff d), (∀ s, (I s).M 0 0 = 1) →
    (∀ s (i : Fin d), i ≠ 0 → (I s).M i 0 = 0) → (∀ ρ ∈ rulesST, NWeak I ρ) →
    ∀ ρ ∈ rulesST, ∀ K : ℕ, ∃ n, K ≤ n ∧ ∃ m : ℕ,
      (∀ i < m, 2 ≤ T^[i] n) ∧ PhiN I (can n) < usesOrbit ρ n m

/-- The value-level cores are equivalent also when restricted to the source form (so this form may be chosen as the target of the proof). -/
theorem natValueCoreSrc_iff : NatValueCoreSrc ↔ NatValueCore := by
  constructor
  · intro h
    refine natValueCore_of_core' (natValueCore'_of_genValueCore ?_)
    intro ι _ _ N a z hweak ρ hρ K
    obtain ⟨n, hn, m, horb, hlt⟩ := h (Fintype.card ι + 1) (embInterp N a z) (embInterp_M00 N a z)
      (embInterp_col0 N a z) (embInterp_weak N a z hweak) ρ hρ K
    exact ⟨n, hn, m, horb, by rwa [embInterp_phi] at hlt⟩
  · intro h d _ I h00 _ hweak
    exact h d I (fun s => (h00 s).ge) hweak

/-! ## §5 Transposition fits the form for general families (Lemma 10.4 of the paper; the reversed statements are in later files) -/

/-- Reversing both sides of a rule (the rules of the reversed system of Def 2.7 of YAH). -/
def ruleRev (ρ : Rule) : Rule := ⟨ρ.lhs.reverse, ρ.rhs.reverse⟩

section Transpose

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The products of words of the transposed family are the transposes of the products of the reversed words: `N'_w = (N_{rev w})^T` (`N'_s := N_s^T`). -/
theorem NW_transpose (N : Letter → Matrix ι ι ℕ) :
    ∀ w : Word, NW (fun s => (N s)ᵀ) w = (NW N w.reverse)ᵀ
  | [] => by simp
  | s :: w => by
    rw [NW_cons, NW_transpose N w, List.reverse_cons, NW_append, NW_singleton, Matrix.transpose_mul]

/-- **Transposition**: the transposed family weakly orients a rule `ρ` entrywise if and only if the original family weakly orients the reversed rule `ruleRev ρ`.
So for a natural-number matrix interpretation `I` that weakly orients the 11 rules of 𝒯^rev, the family of transposed homogeneous matrices
`fun s => (homN (I s))ᵀ` (`a = none`, `z = some 0`) satisfies the premise of `GenValueCore`, and its value is
`(N'_{can n})_{none, some 0} = (N_{rev (can n)})_{some 0, none} = Φ^rev(n)` (`NW_transpose`). -/
theorem gweak_transpose_iff (N : Letter → Matrix ι ι ℕ) (ρ : Rule) :
    GWeak (fun s => (N s)ᵀ) ρ ↔ GWeak N (ruleRev ρ) := by
  unfold GWeak ruleRev
  simp only [NW_transpose, Matrix.transpose_apply]
  exact ⟨fun h i j => h j i, fun h i j => h j i⟩

end Transpose

/-- The value of the transposition: `Φ^rev(n) := ([rev (can n)](0))_0` is the `(none, some 0)` entry of the family of transposed homogeneous matrices. -/
theorem phiN_rev_eq_transpose {d : ℕ} [NeZero d] (I : Letter → NAff d) (n : ℕ) :
    PhiN I (can n).reverse = NW (fun s => (homFam I s)ᵀ) (can n) none (some 0) := by
  rw [NW_transpose, Matrix.transpose_apply, phiN_eq_nw]

end Collatz.Arctic.NatQ5
