/-
Lineages and stages in the proof of Lemma 6.6 of the paper. The steps "one stage" (growth on each interval), "two stages" (concatenation) and the lift at time `T`
in the proof of Lemma 6.6, written on top of Lemma 6.3 (`Transport.lean`, `TransportStay.lean`).
The parts are in `LowerPath.lean`.

* Invariant `LowInv P i R`: at the time `P` of the end of an occurrence of `u*`, all indices of `β_i` have finite values at least `R`.
* `lineage_step` (Lemma 6.3 (ii), (iii)): for `j := π_{typ W}(i)` and every index `k` of `Q_j`, there is a path from an index of `β_i ∩ C(i)` that
  reads `W` inside `C(i)` only and reaches `k` by `u*`. Corollary: the process restricted to `C(i)` started from `β_i ∩ C(i)`
  never dies (`neverDies_beta`). Since `C(π(i)) = C(i)`, the rate does not change either (`classRate_piX`).
* `lowInv_lift` (lift), `lowInv_init` (at the end of the first occurrence the values are at least 0).
* `hitSet_step` (transport of the upper set): the classes hit at time `Q₀ u* W` are images under `π_{typ W}` of the classes hit at time `Q₀`.
* `lowInv_stage` (stage): if the values on `β_i` are at least `R` at time `P`, then after reading a digit word `c B d` (`B` a good word) and `u*`
  the values on `β_{π(i)}` are at least `R + (Λ_{C(i)} - ε')|B|` (`π := π_{typ(c B d)}`).
* `lower_det`, `lower_of_good`: the deterministic part that joins the two intervals.

Remark on the method: instead of starting the restricted process at the end of the first occurrence of `u*` in the interval (a stopping time) and using the strong
Markov property, we use the deterministic condition "the first `m` letters of the interval contain an occurrence of `u*`, and the rest (the part starting at a fixed position) is a good word".
The remainder `c` of the first part after the occurrence is treated as an arbitrary digit word, and `HSP` is applied to the component `C(i)` and to the support of the
restricted process after reading `c` from `β_i ∩ C(i)` (that support never dies either; the pairs `(C, S)` satisfying the premise are finitely many, so the fraction of words
that are good for all of them simultaneously is bounded by `HSP`). In this way no count of the decompositions of words at a stopping time is needed.
-/
import CollatzProof.Arctic.LowerPath

namespace Collatz.Arctic.Lower

open MinIdeal Matrix

variable {D : ℕ}

section Lineage

variable {A : Interp D} {K : Set (BRel (Fin D))} {E : BRel (Fin D)}
  (hK : IsMinIdeal (Mon (B0 A) (B1 A)) K) (hEK : E ∈ K) (hE : E * E = E)

/-- Invariant: at time `P` (the end of an occurrence of `u*`), all indices of `β_i` have finite values at least `R`. -/
def LowInv (u : Fin D → Arc) (A : Interp D) (P : Word) (i : Cls E hE) (R : ℝ) : Prop :=
  ∀ n, beta hE i n → ∃ v : ℕ, vecAfter u A P n = Arc.fin v ∧ R ≤ v

include hK hEK in
/-- **One step of a lineage** (Lemma 6.3 (ii), (iii)): for a digit word `W` and `j := π_{typ W}(i)`,
for every index `k` of `Q_j` there is an index `s`, reached from an index `m` of `β_i ∩ C(i)` by reading `W` inside `C(i)` only, from which `u*` leads to
`k`. -/
theorem lineage_step (i : Cls E hE) {C : Finset (Fin D)}
    (hC : ∀ a, a ∈ C ↔ a ∈ comp (B0 A) (B1 A) hE i) (W : Word) (hW : IsDigits W)
    {k : Fin D} (hk : E k k) (hkc : cls hE k hk = piX hE (suppRel (ev A W)) i) :
    ∃ m, beta hE i m ∧ m ∈ C ∧ ∃ s ∈ C, ev (restrictI C A) W m s ≠ 0 ∧ E s k := by
  have hEM : E ∈ Mon (B0 A) (B1 A) := hK.1.2.1 hEK
  have hXM : suppRel (ev A W) ∈ Mon (B0 A) (B1 A) := suppRel_ev_mem A W hW
  have hX : InH E (E * suppRel (ev A W) * E) := inH_of_minIdeal hK hEK hE hXM
  obtain ⟨k₀, hk₀, hk₀i⟩ := cls_surj hE i
  have hcomp : comp (B0 A) (B1 A) hE (cls hE k hk) = comp (B0 A) (B1 A) hE i := by
    rw [hkc]; exact comp_piX hE hEM hXM hX i
  have hkC : k ∈ comp (B0 A) (B1 A) hE (cls hE k₀ hk₀) := by
    rw [hk₀i, ← hcomp]
    exact ⟨k, hk, rfl, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  obtain ⟨hkk₀, -⟩ := (mem_comp_iff hE hEM hk₀ k).1 hkC
  have hrow := congrFun (piX_spec hE hX k₀ hk₀) k
  rw [hk₀i, ← hkc, beta_cls] at hrow
  have hEXE : (E * suppRel (ev A W) * E) k₀ k := by rw [hrow]; exact hk
  obtain ⟨s, hk₀s, hsk⟩ := (BRel.mul_apply _ _ _ _).1 hEXE
  obtain ⟨m, hk₀m, hms⟩ := (BRel.mul_apply _ _ _ _).1 hk₀s
  have rk₀m := reach_of_mem hEM k₀ m hk₀m
  have rms := reach_of_mem hXM m s hms
  have rsk := reach_of_mem hEM s k hsk
  have hmC : m ∈ C := by
    rw [hC, ← hk₀i, mem_comp_iff hE hEM hk₀]
    exact ⟨rms.trans (rsk.trans hkk₀), rk₀m⟩
  have hsC : s ∈ C := by
    rw [hC, ← hk₀i, mem_comp_iff hE hEM hk₀]
    exact ⟨rsk.trans hkk₀, rk₀m.trans rms⟩
  refine ⟨m, ?_, hmC, s, hsC, ?_, hsk⟩
  · rw [← hk₀i, beta_cls]; exact hk₀m
  · exact ev_restrict_ne_zero A (pathConvex_comp hE hEM i hC) W hW hmC hsC hms

open Classical in
include hK hEK in
/-- The process restricted to `C(i)` started from `β_i ∩ C(i)` never dies. -/
theorem neverDies_beta (i : Cls E hE) {C : Finset (Fin D)}
    (hC : ∀ a, a ∈ C ↔ a ∈ comp (B0 A) (B1 A) hE i) :
    NeverDies A C (C.filter (fun n => beta hE i n)) := by
  intro w hw
  obtain ⟨k, hk, hkc⟩ := cls_surj hE (piX hE (suppRel (ev A w)) i)
  obtain ⟨m, hm, hmC, s, -, hms, -⟩ := lineage_step hK hEK hE i hC w hw hk hkc
  exact ⟨m, Finset.mem_filter.2 ⟨hmC, hm⟩, s, hms⟩

open Classical in
include hK hEK in
/-- The rate of a class does not change under transport (`C(π(i)) = C(i)`). -/
lemma classRate_piX {X : BRel (Fin D)} (hXM : X ∈ Mon (B0 A) (B1 A)) (i : Cls E hE) :
    classRate hE A (piX hE X i) = classRate hE A i := by
  have hEM := hK.1.2.1 hEK
  have hX := inH_of_minIdeal hK hEK hE hXM
  obtain ⟨C, hC, hr⟩ : ∃ C : Finset (Fin D), (∀ a, a ∈ C ↔ a ∈ comp (B0 A) (B1 A) hE i) ∧
      classRate hE A i = rate A C := ⟨_, fun a => Set.mem_toFinset, rfl⟩
  obtain ⟨C', hC', hr'⟩ : ∃ C : Finset (Fin D),
      (∀ a, a ∈ C ↔ a ∈ comp (B0 A) (B1 A) hE (piX hE X i)) ∧
      classRate hE A (piX hE X i) = rate A C := ⟨_, fun a => Set.mem_toFinset, rfl⟩
  rw [hr, hr']
  congr 1
  ext a
  rw [hC, hC', comp_piX hE hEM hXM hX]

/-- **Lift**: if the index `s` has value `x` at time `P` and `u*` leads from `s` to all of `β_j`,
then at time `P u*` all indices of `β_j` have values at least `x`. -/
lemma lowInv_lift {u : Fin D → Arc} (ustar : Word) (huE : suppRel (ev A ustar) = E) {P : Word}
    {s : Fin D} {x : ℕ} (hs : vecAfter u A P s = Arc.fin x) {j : Cls E hE}
    (hsj : ∀ n, beta hE j n → E s n) (R : ℝ) (hR : R ≤ x) :
    LowInv hE u A (P ++ ustar) j R := by
  intro n hn
  have hsn : ev A ustar s n ≠ 0 := by
    have : suppRel (ev A ustar) s n := by rw [huE]; exact hsj n hn
    exact this
  obtain ⟨y, hy⟩ := arc_exists_fin hsn
  obtain ⟨v, hv, hle⟩ := vec_step (MLe.refl _) hs hy
  refine ⟨v, hv, hR.trans ?_⟩
  exact_mod_cast (Nat.le_add_right x y).trans hle

/-- Invariant at the end of the first occurrence: the values on `β` of the occupied classes are at least 0 (finite). -/
lemma lowInv_init {u : Fin D → Arc} (ustar : Word) (huE : suppRel (ev A ustar) = E) {Q₀ : Word}
    {i : Cls E hE} (hi : i ∈ hitSet hE (suppV (vecAfter u A Q₀))) :
    LowInv hE u A (Q₀ ++ ustar) i 0 := by
  obtain ⟨s, hs, k, hk, hki, hsk⟩ := hi
  obtain ⟨x, hx⟩ := arc_exists_fin (show vecAfter u A Q₀ s ≠ 0 from hs)
  refine lowInv_lift hE ustar huE hx (fun n hn => ?_) 0 (Nat.cast_nonneg x)
  rw [← hki, beta_cls] at hn
  exact trans_of_idem hE hsk hn

include hK hEK in
/-- **Transport of the upper set** (Lemma 6.3 (i)): every class hit at time `Q₀ u* W` is the image under `π_{typ W}` of a class hit
at time `Q₀`. -/
theorem hitSet_step (u : Fin D → Arc) (ustar : Word) (huE : suppRel (ev A ustar) = E)
    (Q₀ W : Word) (hW : IsDigits W) {j : Cls E hE}
    (hj : j ∈ hitSet hE (suppV (vecAfter u A (Q₀ ++ ustar ++ W)))) :
    ∃ i ∈ hitSet hE (suppV (vecAfter u A Q₀)), piX hE (suppRel (ev A W)) i = j := by
  have hXM := suppRel_ev_mem A W hW
  have hX : InH E (E * suppRel (ev A W) * E) := inH_of_minIdeal hK hEK hE hXM
  have h2 : suppV (vecAfter u A (Q₀ ++ ustar ++ W)) =
      act (betaUnion hE (hitSet hE (suppV (vecAfter u A Q₀)))) (suppRel (ev A W)) := by
    rw [vecAfter_append, suppV_vecAfter, vecAfter_append, suppV_vecAfter, huE,
      act_E_eq_betaUnion hE]
  have h3 : hitSet hE (act (betaUnion hE (hitSet hE (suppV (vecAfter u A Q₀)))) (suppRel (ev A W)))
      = piX hE (suppRel (ev A W)) '' hitSet hE (suppV (vecAfter u A Q₀)) := by
    apply upperSet_unique hE (hitSet_isUpperSet hE _)
      (piX_isUpperSet hE _ (hitSet_isUpperSet hE _))
    rw [← act_E_eq_betaUnion hE, act_betaUnion hE hX]
  rw [h2, h3] at hj
  obtain ⟨i, hi, rfl⟩ := hj
  exact ⟨i, hi, rfl⟩

open Classical in
include hK hEK in
/-- **Stage** ("one stage" and "two stages" in the proof of Lemma 6.6): if at time `P` (the end of an occurrence of `u*`)
the values on `β_i` are at least `R`, then after reading a digit word `c B d` (`B` a good word) and `u*` the values on `β_{π(i)}` are
at least `R + (Λ_{C(i)} - ε')|B|` (`π := π_{typ(c B d)}`). -/
theorem lowInv_stage (u : Fin D → Arc) (ustar : Word) (huE : suppRel (ev A ustar) = E) {P : Word}
    {i : Cls E hE} {R : ℝ} (hinv : LowInv hE u A P i R) {c B d : Word} (hc : IsDigits c)
    (hB : IsDigits B) (hd : IsDigits d) {ε' : ℝ} (hgood : SPGood A ε' B) :
    LowInv hE u A (P ++ (c ++ B ++ d) ++ ustar) (piX hE (suppRel (ev A (c ++ B ++ d))) i)
      (R + (classRate hE A i - ε') * B.length) := by
  have hEM : E ∈ Mon (B0 A) (B1 A) := hK.1.2.1 hEK
  obtain ⟨C, hC, hrate⟩ : ∃ C : Finset (Fin D), (∀ a, a ∈ C ↔ a ∈ comp (B0 A) (B1 A) hE i) ∧
      classRate hE A i = rate A C := ⟨_, fun a => Set.mem_toFinset, rfl⟩
  rw [hrate]
  have hW : IsDigits (c ++ B ++ d) := isDigits_append (isDigits_append hc hB) hd
  obtain ⟨k, hk, hkc⟩ := cls_surj hE (piX hE (suppRel (ev A (c ++ B ++ d))) i)
  obtain ⟨m, hmi, hmC, s, -, hms, hsk⟩ := lineage_step hK hEK hE i hC (c ++ B ++ d) hW hk hkc
  rw [ev_append, ev_append, mul_apply_ne_zero_iff] at hms
  obtain ⟨b, hmb, hbs⟩ := hms
  rw [mul_apply_ne_zero_iff] at hmb
  obtain ⟨a, hma, hab⟩ := hmb
  set S₀ := C.filter (fun n => beta hE i n) with hS₀
  set S₁ := C.filter (fun a => ∃ n ∈ S₀, ev (restrictI C A) c n a ≠ 0) with hS₁
  have hmS₀ : m ∈ S₀ := Finset.mem_filter.2 ⟨hmC, hmi⟩
  have haS₁ : a ∈ S₁ := Finset.mem_filter.2 ⟨ev_restrict_mem C A c hma hmC, m, hmS₀, hma⟩
  have hND : NeverDies A C S₁ :=
    neverDies_after (neverDies_beta hK hEK hE i hC) (Finset.filter_subset _ _) c hc
  have hrow_ne : rowVal A C S₁ B b ≠ 0 := by
    unfold rowVal; rw [Arc.sum_ne_zero_iff]; exact ⟨a, haS₁, hab⟩
  obtain ⟨v', hv'⟩ := arc_exists_fin hrow_ne
  have hv'le : (rate A C - ε') * B.length ≤ v' :=
    hgood C S₁ (strongConn_comp hE hEM i hC) (Finset.filter_subset _ _) ⟨a, haS₁⟩ hND b v' hv'
  obtain ⟨a', ha'S₁, ha'eq⟩ := Arc.exists_eq_sum ⟨a, haS₁⟩ (fun a => ev (restrictI C A) B a b)
  have ha'v : ev (restrictI C A) B a' b = Arc.fin v' := by rw [ha'eq]; exact hv'
  obtain ⟨-, n, hnS₀, hna'⟩ := Finset.mem_filter.1 ha'S₁
  obtain ⟨x, hx, hRx⟩ := hinv n (Finset.mem_filter.1 hnS₀).2
  obtain ⟨y₁, hy₁⟩ := arc_exists_fin hna'
  obtain ⟨x₁, hx₁, hle₁⟩ := vec_step (ev_restrict_le C A c) hx hy₁
  obtain ⟨x₂, hx₂, hle₂⟩ := vec_step (ev_restrict_le C A B) hx₁ ha'v
  obtain ⟨y₃, hy₃⟩ := arc_exists_fin hbs
  obtain ⟨x₃, hx₃, hle₃⟩ := vec_step (ev_restrict_le C A d) hx₂ hy₃
  have hPW : P ++ (c ++ B ++ d) = P ++ c ++ B ++ d := by simp
  rw [hPW]
  refine lowInv_lift hE ustar huE hx₃ (fun n' hn' => ?_) _ ?_
  · rw [← hkc, beta_cls] at hn'
    exact trans_of_idem hE hsk hn'
  · have : (x : ℝ) + v' ≤ x₃ := by exact_mod_cast (by omega : x + v' ≤ x₃)
    linarith

end Lineage


section Main

variable {A : Interp D} {K : Set (BRel (Fin D))} {E : BRel (Fin D)}
  (hK : IsMinIdeal (Mon (B0 A) (B1 A)) K) (hEK : E ∈ K) (hE : E * E = E)

lemma LowInv.mono {u : Fin D → Arc} {P : Word} {i : Cls E hE} {R R' : ℝ}
    (h : LowInv hE u A P i R) (hR : R' ≤ R) : LowInv hE u A P i R' := by
  intro n hn
  obtain ⟨v, hv, hle⟩ := h n hn
  exact ⟨v, hv, hR.trans hle⟩

include hK hEK in
/-- **Deterministic part (two intervals)**: for a word `Q₀ u* (c₁ B₁ d₁) u* (c₂ B₂ d₂) u*` with good words `B₁`, `B₂`,
the values on `β_j` for a class `j` hit before the last `u*` are at least `(Λ_{C(j)} - ε')(|B₁| + |B₂|)` after the last `u*`. -/
theorem lower_det (u : Fin D → Arc) (ustar : Word) (huE : suppRel (ev A ustar) = E) {ε' : ℝ}
    (Q₀ c₁ B₁ d₁ c₂ B₂ d₂ : Word) (hc₁ : IsDigits c₁) (hB₁ : IsDigits B₁) (hd₁ : IsDigits d₁)
    (hc₂ : IsDigits c₂) (hB₂ : IsDigits B₂) (hd₂ : IsDigits d₂)
    (hg₁ : SPGood A ε' B₁) (hg₂ : SPGood A ε' B₂) {j : Cls E hE}
    (hj : j ∈ hitSet hE (suppV (vecAfter u A
      (Q₀ ++ ustar ++ (c₁ ++ B₁ ++ d₁) ++ ustar ++ (c₂ ++ B₂ ++ d₂))))) :
    LowInv hE u A (Q₀ ++ ustar ++ (c₁ ++ B₁ ++ d₁) ++ ustar ++ (c₂ ++ B₂ ++ d₂) ++ ustar) j
      ((classRate hE A j - ε') * (B₁.length + B₂.length)) := by
  have hW₁ : IsDigits (c₁ ++ B₁ ++ d₁) := isDigits_append (isDigits_append hc₁ hB₁) hd₁
  have hW₂ : IsDigits (c₂ ++ B₂ ++ d₂) := isDigits_append (isDigits_append hc₂ hB₂) hd₂
  obtain ⟨i₂, hi₂, rfl⟩ := hitSet_step hK hEK hE u ustar huE _ _ hW₂ hj
  obtain ⟨i₁, hi₁, rfl⟩ := hitSet_step hK hEK hE u ustar huE _ _ hW₁ hi₂
  have h0 := lowInv_init hE ustar huE hi₁
  have h1 := lowInv_stage hK hEK hE u ustar huE h0 hc₁ hB₁ hd₁ hg₁
  have h2 := lowInv_stage hK hEK hE u ustar huE h1 hc₂ hB₂ hd₂ hg₂
  rw [classRate_piX hK hEK hE (suppRel_ev_mem A _ hW₁)] at h2
  rw [classRate_piX hK hEK hE (suppRel_ev_mem A _ hW₂),
    classRate_piX hK hEK hE (suppRel_ev_mem A _ hW₁)]
  exact LowInv.mono hE h2 (le_of_eq (by ring))

include hK hEK in
/-- For a word `ω = g₀ B₁ g₁ B₂ y z` such that the first `m_l` letters of `B_l` contain `u*` and the rest is a good word, the values on `β_p` at time
`T := |ω| - |z|` are at least `(Λ_{C(j)} - ε')(|B₁| - m₁ + |B₂| - m₂)` (`j ≤ p`, `j ∈ I`). -/
theorem lower_of_good (u : Fin D → Arc) (ustar : Word) (huE : suppRel (ev A ustar) = E)
    (y z : Word) (hy : IsDigits y) (hyu : ustar <:+ y) {ε' : ℝ} (g₀ g₁ B₁ B₂ : Word)
    (hg₁ : IsDigits g₁) (hB₁ : IsDigits B₁) (hB₂ : IsDigits B₂) (m₁ m₂ : ℕ)
    (hi₁ : ustar <:+: B₁.take m₁) (hgood₁ : SPGood A ε' (B₁.drop m₁))
    (hi₂ : ustar <:+: B₂.take m₂) (hgood₂ : SPGood A ε' (B₂.drop m₂)) :
    ∀ p ∈ hitSet hE (suppV (vecAfter u A ((g₀ ++ B₁ ++ g₁ ++ B₂ ++ y ++ z).take
        ((g₀ ++ B₁ ++ g₁ ++ B₂ ++ y ++ z).length - z.length - ustar.length)))),
      ∀ j ∈ hitSet hE (suppV (vecAfter u A ((g₀ ++ B₁ ++ g₁ ++ B₂ ++ y ++ z).take
        ((g₀ ++ B₁ ++ g₁ ++ B₂ ++ y ++ z).length - z.length - ustar.length)))), j ≤ p →
      ∀ b, beta hE p b → ∀ v : ℕ, vecAfter u A ((g₀ ++ B₁ ++ g₁ ++ B₂ ++ y ++ z).take
        ((g₀ ++ B₁ ++ g₁ ++ B₂ ++ y ++ z).length - z.length)) b = Arc.fin v →
      (classRate hE A j - ε') * ((B₁.drop m₁).length + (B₂.drop m₂).length) ≤ v := by
  obtain ⟨a₁, c₁, h₁⟩ := hi₁
  obtain ⟨a₂, c₂, h₂⟩ := hi₂
  obtain ⟨y', hy'⟩ := hyu
  have e₁ : B₁ = a₁ ++ ustar ++ c₁ ++ B₁.drop m₁ := by rw [h₁]; exact (List.take_append_drop m₁ B₁).symm
  have e₂ : B₂ = a₂ ++ ustar ++ c₂ ++ B₂.drop m₂ := by rw [h₂]; exact (List.take_append_drop m₂ B₂).symm
  generalize B₁.drop m₁ = B₁'' at e₁ hgood₁ ⊢
  generalize B₂.drop m₂ = B₂'' at e₂ hgood₂ ⊢
  subst e₁ e₂ hy'
  have hdB₁ := hB₁
  have hdB₂ := hB₂
  simp only [List.append_assoc] at hdB₁ hdB₂ hy
  have hc₁ : IsDigits c₁ := isDigits_of_append_left (isDigits_of_append_right
    (isDigits_of_append_right hdB₁))
  have hB₁'' : IsDigits B₁'' := isDigits_of_append_right (isDigits_of_append_right
    (isDigits_of_append_right hdB₁))
  have ha₂ : IsDigits a₂ := isDigits_of_append_left hdB₂
  have hc₂ : IsDigits c₂ := isDigits_of_append_left (isDigits_of_append_right
    (isDigits_of_append_right hdB₂))
  have hB₂'' : IsDigits B₂'' := isDigits_of_append_right (isDigits_of_append_right
    (isDigits_of_append_right hdB₂))
  have hy'd : IsDigits y' := isDigits_of_append_left hy
  set Pfx := g₀ ++ a₁ ++ ustar ++ (c₁ ++ B₁'' ++ (g₁ ++ a₂)) ++ ustar ++ (c₂ ++ B₂'' ++ y')
    with hPfx
  have hω : g₀ ++ (a₁ ++ ustar ++ c₁ ++ B₁'') ++ g₁ ++ (a₂ ++ ustar ++ c₂ ++ B₂'') ++
      (y' ++ ustar) ++ z = Pfx ++ ustar ++ z := by
    rw [hPfx]; simp only [List.append_assoc]
  rw [hω]
  have ht1 : (Pfx ++ ustar ++ z).take ((Pfx ++ ustar ++ z).length - z.length - ustar.length)
      = Pfx := by
    rw [List.append_assoc, List.take_left']
    simp only [List.length_append]; omega
  have ht2 : (Pfx ++ ustar ++ z).take ((Pfx ++ ustar ++ z).length - z.length) = Pfx ++ ustar := by
    rw [List.take_left']
    simp only [List.length_append]; omega
  rw [ht1, ht2]
  intro p _ j hj hjp b hb v hv
  have hinv := lower_det hK hEK hE u ustar huE (g₀ ++ a₁) c₁ B₁'' (g₁ ++ a₂) c₂ B₂'' y'
    hc₁ hB₁'' (isDigits_append hg₁ ha₂) hc₂ hB₂'' hy'd hgood₁ hgood₂ hj
  obtain ⟨v', hv', hle⟩ := hinv b ((beta_subset_iff hE j p).2 hjp b hb)
  rw [hv] at hv'
  have : v = v' := by
    have := congrArg Arc.val hv'
    simp only [Arc.val_fin] at this
    exact_mod_cast this
  subst this
  exact hle

end Main

end Collatz.Arctic.Lower
