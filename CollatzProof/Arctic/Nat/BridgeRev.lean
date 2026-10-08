/-
# 𝒯^rev: from mirroring, transposition and the value-level core to the reversed statements

From Lemma 10.4 (transposition), Lemma 13.1 (the bridge and the numbers of uses, mirroring), Lemma 10.5 (the value embedding, `embInterp` of `Embed.lean`) of the paper and
the value-level core (`NatValueCore`, `NatValueCore'` of `Statement.lean`, `GenValueCore` of `Embed.lean`) we derive `NatBarrierSTrev`
(Theorem 9.2 (i) for 𝒯^rev) and `NatBarrierSTrevTop` (Theorem 9.2 (ii) for 𝒯^rev) of `StatementRev.lean`.

* §1 Mirroring (Lemma 13.1 (i)): a step `p ℓ q → p r q` of 𝒯 gives the step `q^rev ℓ^rev p^rev → q^rev r^rev p^rev` of 𝒯^rev
  (`step_rev`), and likewise for derivations (`chain_rev`). So `canDerivRev n` is a derivation `rev (can n) →* rev (can (T n))`
  (`canDerivRev_chain`), and the number of occurrences of the rule `ρ^rev` in it is that of `ρ` in `canDeriv n` (`count_canDerivRev`; reversal is injective).
* §2 Bounds on values (Lemma 13.1 (ii)): `Φ^rev(n) := Φ(rev (can n))`. If all 11 rules are weakly oriented, then
  `Φ^rev(T n) ≤ Φ^rev(n)` (without monotonicity, `phiRev_T_le`). If the interpretation is monotone and strictly orients `ρ^rev`, then
  `Φ^rev(T^m n) + #_ρ(n, m) ≤ Φ^rev(n)` (`orbit_bound_rev`; `phiN_chain_count` of `Bridge.lean` does not depend on the set of rules,
  so it applies directly to the mirrored derivations).
* §3 The top (the reason for Theorem 9.2 (ii) for 𝒯^rev; Lemma 13.1 (iii)): every string of the mirrored canonical derivations has the form "`.` (`rgt`) first, and no other `.`"
  (`TopWordR`), and the rules of 𝒯^rev preserve this form (`topWordR_step`). The left-hand sides of `.f → .` and `.t → .2` begin with `.`, so
  they apply only at positions with empty left context (the top), and without monotonicity `Φ` decreases by at least 1 at each use (`phiN_step_strict_top`
  of `BridgeTop.lean`). `orbit_bound_revTop`.
* §4 Transposition (Lemma 10.4): `N'_s := (N_s)^T` (`N_s` are the homogeneous matrices). The weak orientation of the 11 rules of 𝒯^rev is equivalent to the entrywise weak orientation of
  the 11 rules of 𝒯 by `N'` (`gweak_transpose_of_rev`, `nweak_rev_iff_transpose`); strict orientation adds
  `(N'_ℓ)_{d0} > (N'_r)_{d0}` (`nstrict_rev_iff_transpose`, a remark of the internal review; not needed for the proof of the main theorem). The
  homogeneous index of `N'` is a source (`transpose_col_none`). `Φ^rev(n) = (N'_{can n})_{d0}` is `phiN_rev_eq_transpose`.
* §5 The main theorem: applying `GenValueCore` (= `NatValueCore`, by `genValueCore_iff`) to `N'`, `a = none` (the homogeneous index `d`) and
  `z = some 0` gives `n, m` with `Φ^rev(n) < #_ρ(n, m)`, contradicting the bounds of §2 and §3
  (`natBarrierSTrev_of_genCore`, `natBarrierSTrevTop_of_genCore`). `GenValueCore` has been proved from `NatValueCore` by the embedding of Lemma 10.5
  (the general form that adds both the source `a*` and the sink `s*`). An earlier written proof of Theorem 9.2 (i) for 𝒯^rev adds only the sink `s*` to the
  co-affine form, but adding both gives the same values and weak orientation (a note on a special case of the embedding).
-/
import CollatzProof.Arctic.Nat.StatementRev
import CollatzProof.Arctic.Nat.Embed

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic Matrix Letter

namespace W5

/-! ## §0 Basic facts on reversal -/

theorem rulesSTrev_eq_map : rulesSTrev = rulesST.map ruleRev := rfl

theorem canDerivRev_eq_map (n : ℕ) : canDerivRev n = (canDeriv n).map ruleRev := rfl

theorem ruleRev_ruleRev (ρ : Rule) : ruleRev (ruleRev ρ) = ρ := by
  cases ρ; simp [ruleRev]

theorem ruleRev_injective : Function.Injective ruleRev := fun a b h => by
  rw [← ruleRev_ruleRev a, h, ruleRev_ruleRev]

theorem ruleRev_mem_rulesSTrev {ρ : Rule} (hρ : ρ ∈ rulesST) : ruleRev ρ ∈ rulesSTrev :=
  List.mem_map_of_mem hρ

theorem mem_rulesSTrev {ρ' : Rule} (h : ρ' ∈ rulesSTrev) : ∃ ρ ∈ rulesST, ρ' = ruleRev ρ := by
  obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 h
  exact ⟨ρ, hρ, rfl⟩

theorem rulesSTrevTop_sub : ∀ ρ ∈ rulesSTrevTop, ρ ∈ rulesSTrev := by decide

/-- The top rules are the reversals of the dynamic rules of 𝒯 (entries 0 and 1). -/
theorem rulesSTrevTop_eq : rulesSTrevTop = [ruleRev ⟨[f, rgt], [rgt]⟩, ruleRev ⟨[t, rgt], [d2, rgt]⟩] := rfl

/-! ## §1 Mirroring (Lemma 13.1 (i)) -/

/-- The mirror image of one step: if `p ℓ q → p r q` (by the rule `ρ`), then `q^rev ℓ^rev p^rev → q^rev r^rev p^rev` (by the rule `ρ^rev`). -/
theorem step_rev {ρ : Rule} {u v : Word} (h : Step ρ u v) : Step (ruleRev ρ) u.reverse v.reverse := by
  obtain ⟨p, q, rfl, rfl⟩ := h
  exact ⟨q.reverse, p.reverse, by simp [ruleRev, List.reverse_append, List.append_assoc],
    by simp [ruleRev, List.reverse_append, List.append_assoc]⟩

/-- The mirror image of a derivation. -/
theorem chain_rev : ∀ {rs : List Rule} {u v : Word}, Chain rs u v → Chain (rs.map ruleRev) u.reverse v.reverse := by
  intro rs u v h
  induction h with
  | nil u => exact Chain.nil _
  | cons hstep _ ih => exact Chain.cons (step_rev hstep) ih

/-- **Correctness of the mirrored canonical derivation**: for `n ≥ 2`, `canDerivRev n` is a derivation of 𝒯^rev from `rev (can n)` to `rev (can (T n))`. -/
theorem canDerivRev_chain (n : ℕ) (hn : 2 ≤ n) : Chain (canDerivRev n) (can n).reverse (can (T n)).reverse :=
  chain_rev (canDeriv_chain n hn)

/-- The rules of the mirrored canonical derivations belong to the 11 rules of 𝒯^rev. -/
theorem canDerivRev_sub (n : ℕ) : ∀ σ ∈ canDerivRev n, σ ∈ rulesSTrev := by
  intro σ hσ
  obtain ⟨τ, hτ, rfl⟩ := List.mem_map.1 hσ
  exact ruleRev_mem_rulesSTrev (canDeriv_sub n τ hτ)

/-- **The numbers of uses are the same**: the number of occurrences of `ρ^rev` in the mirrored canonical derivation is that of `ρ` in the canonical derivation. -/
theorem count_canDerivRev (ρ : Rule) (n : ℕ) : (canDerivRev n).count (ruleRev ρ) = uses ρ n := by
  rw [canDerivRev_eq_map, List.count_map_of_injective _ _ ruleRev_injective]
  rfl

/-! ## §2 Bounds on values (Lemma 13.1 (ii)) -/

variable {d : ℕ}

theorem orbit_tail {n m : ℕ} (horb : ∀ i < m + 1, 2 ≤ T^[i] n) : 2 ≤ n ∧ ∀ i < m, 2 ≤ T^[i] (T n) := by
  refine ⟨by simpa using horb 0 (Nat.succ_pos m), fun i hi => ?_⟩
  have := horb (i + 1) (by omega)
  rwa [Function.iterate_succ_apply] at this

/-- **Lemma 13.1 (ii)**, first part (without monotonicity): if all 11 rules of 𝒯^rev are weakly oriented, then `Φ^rev(T n) ≤ Φ^rev(n)` for `n ≥ 2`. -/
theorem phiRev_T_le [NeZero d] {I : Letter → NAff d} (hweak : ∀ ρ ∈ rulesSTrev, NWeak I ρ) (n : ℕ) (hn : 2 ≤ n) :
    PhiN I (can (T n)).reverse ≤ PhiN I (can n).reverse :=
  phiN_chain_le I (canDerivRev_chain n hn) (fun σ hσ => hweak σ (canDerivRev_sub n σ hσ))

/-- On a segment of an orbit (all points at least 2), `Φ^rev` does not increase. -/
theorem phiRev_iterate_le [NeZero d] {I : Letter → NAff d} (hweak : ∀ ρ ∈ rulesSTrev, NWeak I ρ) :
    ∀ (m n : ℕ), (∀ i < m, 2 ≤ T^[i] n) → PhiN I (can (T^[m] n)).reverse ≤ PhiN I (can n).reverse := by
  intro m
  induction m with
  | zero => intro n _; simp
  | succ m ih =>
    intro n horb
    obtain ⟨hn, horb'⟩ := orbit_tail horb
    rw [Function.iterate_succ_apply]
    exact (ih (T n) horb').trans (phiRev_T_le hweak n hn)

/-- **Lemma 13.1 (ii)**, second part: if the interpretation is monotone, weakly orients the 11 rules of 𝒯^rev and strictly orients `ρ^rev`, then
`Φ^rev(T^m n) + #_ρ(n, m) ≤ Φ^rev(n)`. -/
theorem orbit_bound_rev [NeZero d] {I : Letter → NAff d} (hmono : NMono I)
    (hweak : ∀ ρ ∈ rulesSTrev, NWeak I ρ) {ρ : Rule} (hρ : NStrict I (ruleRev ρ)) :
    ∀ (m n : ℕ), (∀ i < m, 2 ≤ T^[i] n) →
      PhiN I (can (T^[m] n)).reverse + usesOrbit ρ n m ≤ PhiN I (can n).reverse := by
  intro m
  induction m with
  | zero => intro n _; simp [usesOrbit_zero]
  | succ m ih =>
    intro n horb
    obtain ⟨hn, horb'⟩ := orbit_tail horb
    have hstep := phiN_chain_count hmono hρ (canDerivRev_chain n hn)
      (fun σ hσ => hweak σ (canDerivRev_sub n σ hσ))
    rw [count_canDerivRev] at hstep
    have hrest := ih (T n) horb'
    rw [Function.iterate_succ_apply, usesOrbit_succ]
    omega

/-! ## §3 The top (Theorem 9.2 (ii) for 𝒯^rev; Lemma 13.1 (iii)) -/

/-- Strings in reversed top form: `.` first, and no other `.`. -/
def TopWordR (u : Word) : Prop := ∃ w, u = rgt :: w ∧ rgt ∉ w

theorem rgt_not_mem_binTail (n : ℕ) : rgt ∉ binTail n := by
  simp only [binTail, List.mem_map, not_exists, not_and]
  intro b _ h
  split_ifs at h

/-- `rev (can n) = . bin'(n)^rev /`. -/
theorem can_reverse (n : ℕ) : (can n).reverse = rgt :: ((binTail n).reverse ++ [lft]) := by
  simp [can, List.reverse_append]

theorem topWordR_can (n : ℕ) : TopWordR (can n).reverse :=
  ⟨(binTail n).reverse ++ [lft], can_reverse n, by simp [rgt_not_mem_binTail]⟩

/-- The form of the top rules: both sides begin with `.` and contain no other `.`. -/
theorem rulesSTrevTop_form : ∀ ρ ∈ rulesSTrevTop,
    ∃ l r : Word, ρ.lhs = rgt :: l ∧ ρ.rhs = rgt :: r ∧ rgt ∉ l ∧ rgt ∉ r := by
  intro ρ hρ
  simp only [rulesSTrevTop, List.mem_cons, List.mem_nil_iff, or_false] at hρ
  rcases hρ with rfl | rfl <;> exact ⟨_, _, rfl, rfl, by decide, by decide⟩

/-- The rules that are not top rules contain no `.`, and their left-hand sides are non-empty. -/
theorem rulesSTrev_nonTop : ∀ ρ ∈ rulesSTrev, ρ ∉ rulesSTrevTop → ρ.lhs ≠ [] ∧ rgt ∉ ρ.lhs ∧ rgt ∉ ρ.rhs := by
  decide

/-- One step by a rule of 𝒯^rev preserves the top form, and the top rules apply only at positions with empty left context (the top). -/
theorem topWordR_step {σ : Rule} (hσ : σ ∈ rulesSTrev) {u v : Word} (hst : Step σ u v) (hu : TopWordR u) :
    TopWordR v ∧ (σ ∈ rulesSTrevTop → ∃ q, u = σ.lhs ++ q ∧ v = σ.rhs ++ q) := by
  obtain ⟨p, q, rfl, rfl⟩ := hst
  obtain ⟨w, hw, hlw⟩ := hu
  by_cases hB : σ ∈ rulesSTrevTop
  · obtain ⟨l, r, hl, hr, hl', hr'⟩ := rulesSTrevTop_form σ hB
    cases p with
    | nil =>
      rw [List.nil_append, hl, List.cons_append, List.cons.injEq] at hw
      obtain ⟨-, rfl⟩ := hw
      refine ⟨⟨r ++ q, by rw [List.nil_append, hr, List.cons_append], ?_⟩, fun _ => ⟨q, by simp, by simp⟩⟩
      simp only [List.mem_append, not_or] at hlw ⊢
      exact ⟨hr', hlw.2⟩
    | cons a p' =>
      exfalso
      rw [hl, List.cons_append, List.cons_append, List.cons.injEq] at hw
      obtain ⟨-, rfl⟩ := hw
      exact hlw (by simp)
  · obtain ⟨hne, hl, hr⟩ := rulesSTrev_nonTop σ hσ hB
    refine ⟨?_, fun h => absurd h hB⟩
    cases p with
    | nil =>
      exfalso
      rw [List.nil_append] at hw
      obtain ⟨a, l', hal⟩ := List.exists_cons_of_ne_nil hne
      rw [hal, List.cons_append, List.cons.injEq] at hw
      exact hl (by rw [hal, hw.1]; exact List.mem_cons_self)
    | cons a p' =>
      rw [List.cons_append, List.cons_append, List.cons.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      refine ⟨p' ++ σ.rhs ++ q, by simp, ?_⟩
      simp only [List.mem_append, not_or] at hlw ⊢
      exact ⟨⟨hlw.1.1, hr⟩, hlw.2⟩

/-- Along derivations of 𝒯^rev that start in top form, `Φ` decreases by at least the number of uses of the strictly oriented top rule `ρ` (without monotonicity). -/
theorem phiN_chain_count_topR [NeZero d] {I : Letter → NAff d} {ρ : Rule} (hρB : ρ ∈ rulesSTrevTop)
    (hρ : NStrict I ρ) :
    ∀ {rs : List Rule} {u v : Word}, Chain rs u v → (∀ σ ∈ rs, σ ∈ rulesSTrev) → (∀ σ ∈ rs, NWeak I σ) →
      TopWordR u → PhiN I v + rs.count ρ ≤ PhiN I u := by
  intro rs u v hc
  induction hc with
  | nil u => intro _ _ _; simp
  | @cons σ rs u w v hstep _ ih =>
    intro hmem hw htop
    obtain ⟨htop', hB⟩ := topWordR_step (hmem σ List.mem_cons_self) hstep htop
    have hrest := ih (fun τ hτ => hmem τ (List.mem_cons_of_mem _ hτ))
      (fun τ hτ => hw τ (List.mem_cons_of_mem _ hτ)) htop'
    by_cases hσ : σ = ρ
    · subst hσ
      obtain ⟨q, rfl, rfl⟩ := hB hρB
      have h1 := phiN_step_strict_top hρ q
      rw [List.count_cons_self]
      omega
    · obtain ⟨p, q, rfl, rfl⟩ := hstep
      have h1 := phiN_step_le (hw σ List.mem_cons_self) p q
      rw [List.count_cons_of_ne hσ]
      omega

/-- A bound along orbits (without monotonicity): if the interpretation weakly orients the 11 rules of 𝒯^rev and strictly orients the top rule `ρ^rev`, then
`Φ^rev(T^m n) + #_ρ(n, m) ≤ Φ^rev(n)`. -/
theorem orbit_bound_revTop [NeZero d] {I : Letter → NAff d} (hweak : ∀ ρ ∈ rulesSTrev, NWeak I ρ) {ρ : Rule}
    (hρB : ruleRev ρ ∈ rulesSTrevTop) (hρ : NStrict I (ruleRev ρ)) :
    ∀ (m n : ℕ), (∀ i < m, 2 ≤ T^[i] n) →
      PhiN I (can (T^[m] n)).reverse + usesOrbit ρ n m ≤ PhiN I (can n).reverse := by
  intro m
  induction m with
  | zero => intro n _; simp [usesOrbit_zero]
  | succ m ih =>
    intro n horb
    obtain ⟨hn, horb'⟩ := orbit_tail horb
    have hstep := phiN_chain_count_topR hρB hρ (canDerivRev_chain n hn) (fun σ hσ => canDerivRev_sub n σ hσ)
      (fun σ hσ => hweak σ (canDerivRev_sub n σ hσ)) (topWordR_can n)
    rw [count_canDerivRev] at hstep
    have hrest := ih (T n) horb'
    rw [Function.iterate_succ_apply, usesOrbit_succ]
    omega

/-! ## §4 Transposition (Lemma 10.4) -/

/-- The family `N'_s := (N_s)^T` of transposed homogeneous matrices (the type of indices is `Option (Fin d)`; `none` is the homogeneous index `d`). -/
def transFam (I : Letter → NAff d) : Letter → Matrix (Option (Fin d)) (Option (Fin d)) ℕ :=
  fun s => (homFam I s)ᵀ

/-- **Lemma 10.4 (ii) (weak orientation)**: weakly orienting `ρ^rev` is equivalent to the entrywise weak orientation of `ρ` by `N'`. -/
theorem nweak_rev_iff_transpose (I : Letter → NAff d) (ρ : Rule) :
    NWeak I (ruleRev ρ) ↔ GWeak (transFam I) ρ := by
  rw [nweak_iff_gweak]
  exact (gweak_transpose_iff (homFam I) ρ).symm

/-- If the 11 rules of 𝒯^rev are weakly oriented, then `N'` weakly orients the 11 rules of 𝒯 entrywise ((G1)). -/
theorem gweak_transpose_of_rev {I : Letter → NAff d} (hweak : ∀ ρ ∈ rulesSTrev, NWeak I ρ) :
    ∀ ρ ∈ rulesST, GWeak (transFam I) ρ := fun ρ hρ =>
  (nweak_rev_iff_transpose I ρ).1 (hweak _ (ruleRev_mem_rulesSTrev hρ))

/-- The converse also holds: if `N'` satisfies (G1), the 11 rules of 𝒯^rev are weakly oriented. -/
theorem rev_weak_of_gweak_transpose {I : Letter → NAff d} (h : ∀ ρ ∈ rulesST, GWeak (transFam I) ρ) :
    ∀ ρ ∈ rulesSTrev, NWeak I ρ := by
  intro ρ' hρ'
  obtain ⟨ρ, hρ, rfl⟩ := mem_rulesSTrev hρ'
  exact (nweak_rev_iff_transpose I ρ).2 (h ρ hρ)

/-- **Lemma 10.4 (i)**: `Φ^rev(n) = (N'_{can n})_{d0}` (`phiN_rev_eq_transpose`). -/
theorem phiRev_eq_transFam [NeZero d] (I : Letter → NAff d) (n : ℕ) :
    PhiN I (can n).reverse = NW (transFam I) (can n) none (some 0) :=
  phiN_rev_eq_transpose I n

/-- The transposed form of the values of words: `Φ(w^rev) = (N'_w)_{d0}`. -/
theorem phiN_reverse_eq_transFam [NeZero d] (I : Letter → NAff d) (w : Word) :
    PhiN I w.reverse = NW (transFam I) w none (some 0) := by
  show PhiN I w.reverse = NW (fun s => (homFam I s)ᵀ) w none (some 0)
  rw [NW_transpose, Matrix.transpose_apply, phiN_eq_nw]

/-- **Lemma 10.4 (iii) (strict orientation; a remark of the internal review)**: strictly orienting `ρ^rev` is equivalent to the entrywise weak orientation of `ρ` by `N'`
together with `(N'_ℓ)_{d0} > (N'_r)_{d0}`. -/
theorem nstrict_rev_iff_transpose [NeZero d] (I : Letter → NAff d) (ρ : Rule) :
    NStrict I (ruleRev ρ) ↔
      GWeak (transFam I) ρ ∧ NW (transFam I) ρ.rhs none (some 0) < NW (transFam I) ρ.lhs none (some 0) := by
  unfold NStrict
  rw [nweak_rev_iff_transpose, ← phiN_eq, ← phiN_eq, ← phiN_reverse_eq_transFam, ← phiN_reverse_eq_transFam]
  rfl

/-- **Lemma 10.4** (the source): the homogeneous index `d` (`none`) of `N'` is a source: the `d`-th column is `e_d`. -/
theorem transpose_col_none (I : Letter → NAff d) (s : Letter) (p : Option (Fin d)) :
    transFam I s p none = if p = none then 1 else 0 := by
  show homN (I s) none p = _
  rw [homN_none]

/-- Lemma 10.4 (the end index): monotonicity is `(N'_s)_{00} ≥ 1`. -/
theorem transpose_diag0 [NeZero d] (I : Letter → NAff d) (s : Letter) :
    transFam I s (some 0) (some 0) = (I s).M 0 0 := rfl

end W5

/-! ## §5 The main theorem -/

open W5

/-- **Theorem 9.2 (i) for 𝒯^rev from the value-level core for general families**: `NatBarrierSTrev` under `GenValueCore`. -/
theorem natBarrierSTrev_of_genCore (hcore : GenValueCore) : NatBarrierSTrev := by
  intro d _ I hmono hweak ρ' hρ' hs
  obtain ⟨ρ, hρ, rfl⟩ := mem_rulesSTrev hρ'
  obtain ⟨n, -, m, horb, hlt⟩ :=
    hcore (Option (Fin d)) (transFam I) none (some 0) (gweak_transpose_of_rev hweak) ρ hρ 0
  have := orbit_bound_rev hmono hweak hs m n horb
  rw [phiRev_eq_transFam I n] at this
  omega

/-- **Theorem 9.2 (i) for 𝒯^rev**: `NatBarrierSTrev` under the value-level core `NatValueCore`. -/
theorem natBarrierSTrev_of_core (hcore : NatValueCore) : NatBarrierSTrev :=
  natBarrierSTrev_of_genCore (genValueCore_of_natValueCore hcore)

/-- `NatBarrierSTrev` from the value-level core without monotonicity `NatValueCore'` (the form proved later). -/
theorem natBarrierSTrev_of_core' (hcore : NatValueCore') : NatBarrierSTrev :=
  natBarrierSTrev_of_core (natValueCore_of_core' hcore)

/-- **Theorem 9.2 (ii) for 𝒯^rev from the value-level core for general families**: `NatBarrierSTrevTop` under `GenValueCore` (without monotonicity). -/
theorem natBarrierSTrevTop_of_genCore (hcore : GenValueCore) : NatBarrierSTrevTop := by
  intro d _ I hweak ρ' hρ'B hs
  obtain ⟨ρ, hρ, rfl⟩ := mem_rulesSTrev (rulesSTrevTop_sub ρ' hρ'B)
  obtain ⟨n, -, m, horb, hlt⟩ :=
    hcore (Option (Fin d)) (transFam I) none (some 0) (gweak_transpose_of_rev hweak) ρ hρ 0
  have := orbit_bound_revTop hweak hρ'B hs m n horb
  rw [phiRev_eq_transFam I n] at this
  omega

/-- **Theorem 9.2 (ii) for 𝒯^rev**: `NatBarrierSTrevTop` under the value-level core without monotonicity `NatValueCore'`. -/
theorem natBarrierSTrevTop_of_core' (hcore : NatValueCore') : NatBarrierSTrevTop :=
  natBarrierSTrevTop_of_genCore (genValueCore_of_natValueCore (natValueCore_of_core' hcore))

/-- Theorem 9.2 (ii) for 𝒯^rev, also from the monotone form `NatValueCore` of the value-level core (by the equivalence `natValueCore_iff_natValueCore'`). -/
theorem natBarrierSTrevTop_of_core (hcore : NatValueCore) : NatBarrierSTrevTop :=
  natBarrierSTrevTop_of_genCore (genValueCore_of_natValueCore hcore)

/-- The four statements together: from the value-level core, the forward and reversed barriers, and the statements for the forward left-end rules and the reversed top rules. -/
theorem barriers_of_core' (hcore : NatValueCore') :
    NatBarrierST ∧ NatBarrierSTB ∧ NatBarrierSTrev ∧ NatBarrierSTrevTop :=
  ⟨natBarrierST_of_core' hcore, natBarrierSTB_of_core' hcore, natBarrierSTrev_of_core' hcore,
    natBarrierSTrevTop_of_core' hcore⟩

end Collatz.Arctic.NatQ5
