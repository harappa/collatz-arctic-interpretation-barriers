/-
Lean formalization of Lemma 6.3 (i)–(iii) (transport) and Lemma 6.3 (iv) (stay)
(Section 6.2).
Built on the formalization of Lemma 6.2 (`MinIdealBase.lean`, `MinIdeal.lean`).

Setting: a finite set of indices `Q`, relations `B₀, B₁`, the monoid `M` they generate (`Mon B₀ B₁`),
an idempotent `E` of the minimal ideal of `M`, the classes `Cls E hE`, the rows `beta`.

* The support `S·X` obtained by letting the relation `X` act on a support (set of indices) `S` is written `act S X`.
* A "component" is a strongly connected component of the graph of `B₀ ∨ B₁`. Reachability is written `Reach B₀ B₁` (`Relation.ReflTransGen`), and
  the component `C(j)` of a class `j` is "the set of points mutually reachable with the points of `Q_j`", `comp B₀ B₁ hE j`.
* The permutation `π_X` of `X ∈ M` is the choice `piX` from `perm_of_inH` (the identity if `E X E ∉ 𝒢_E`).
  By `perm_unique`, every permutation with the property `(E X E)_q = β_{π [q]}` equals it (`piX_unique`).

Structure: §1 action on supports, unions of `β`, reachability (`reach_of_mem`: the entries 1 of an element of `M` are realized by paths of letters),
§2 one-step transport (`act_betaUnion`, `carry_one`), §3 components (`comp_piX`: `C(π(j)) = C(j)`),
§4 transport along sequences (`act_betaUnion_list`, `carry_list`, `comp_piList`), §5 the stay lemma (`stay`, `stay_supp`),
§6 the word layer (`act_word`: the support after the word `w₀ u x₁ u ⋯ xₙ u`), §7 summary (`lemma_56_10_1`, `lemma_56_10_1_list`,
`corollary_56_10_2`), §8 sanity check (`leRel_comp_ne`).

Remarks:
* The identity of (i) holds even if `I` is not an upper set (`β_i·XE = β_{π(i)}` holds class by class). An upper set is determined by the support
  (`upperSet_unique`), and the upper set of `S·E` is the set `hitSet` of classes hit by `S` (`act_E_eq_betaUnion`).
* (iv) assumes only that the ends `a, b` lie in the same component, not that the path spends the whole occurrence in the component
  (the proof uses only reachability from `b` to `a`). No argument on the DAG of components is needed; transitivity of reachability suffices.
-/
import CollatzProof.Arctic.MinIdeal

namespace Collatz.Arctic.MinIdeal

open BRel

/-! ## 1. Action on supports, unions of `β`, reachability and components -/

section Defs

variable {Q : Type*}

/-- The support `S·X := {k | ∃ s ∈ S, X s k}` obtained by letting the relation `X` act on the support `S`. -/
def act (S : Set Q) (X : BRel Q) : Set Q := {k | ∃ s ∈ S, X s k}

theorem mem_act {S : Set Q} {X : BRel Q} {k : Q} : k ∈ act S X ↔ ∃ s ∈ S, X s k := Iff.rfl

theorem act_mul (S : Set Q) (X Y : BRel Q) : act (act S X) Y = act S (X * Y) := by
  ext k
  simp only [mem_act, mul_apply]
  constructor
  · rintro ⟨m, ⟨s, hs, hsm⟩, hmk⟩; exact ⟨s, hs, m, hsm, hmk⟩
  · rintro ⟨s, hs, m, hsm, hmk⟩; exact ⟨m, ⟨s, hs, hsm⟩, hmk⟩

theorem act_one (S : Set Q) : act S 1 = S := by
  ext k
  simp only [mem_act, one_apply]
  exact ⟨fun ⟨s, hs, h⟩ => h ▸ hs, fun h => ⟨k, h, rfl⟩⟩

/-- The monoid `M` with generators `B₀, B₁`. -/
abbrev Mon (B₀ B₁ : BRel Q) : Submonoid (BRel Q) := Submonoid.closure ({B₀, B₁} : Set (BRel Q))

/-- Reachability in the graph of `B₀ ∨ B₁` (including paths of length 0). -/
def Reach (B₀ B₁ : BRel Q) : Q → Q → Prop :=
  Relation.ReflTransGen (fun a b => B₀ a b ∨ B₁ a b)

theorem Reach.refl' {B₀ B₁ : BRel Q} (a : Q) : Reach B₀ B₁ a a := Relation.ReflTransGen.refl

theorem Reach.trans' {B₀ B₁ : BRel Q} {a b c : Q} (h1 : Reach B₀ B₁ a b) (h2 : Reach B₀ B₁ b c) :
    Reach B₀ B₁ a c := Relation.ReflTransGen.trans h1 h2

/-- The entries 1 of an element of `M` are realized by paths of letters: if `U ∈ M` and `U x y`, then `y` is reachable from `x`. -/
theorem reach_of_mem {B₀ B₁ U : BRel Q} (hU : U ∈ Mon B₀ B₁) : ∀ x y, U x y → Reach B₀ B₁ x y := by
  induction hU using Submonoid.closure_induction with
  | mem V hV =>
    intro x y h
    rcases hV with h0 | h1
    · rw [h0] at h; exact Relation.ReflTransGen.single (Or.inl h)
    · rw [Set.mem_singleton_iff.1 h1] at h; exact Relation.ReflTransGen.single (Or.inr h)
  | one =>
    intro x y h
    rw [one_apply] at h; subst h; exact Relation.ReflTransGen.refl
  | mul V W _ _ hV hW =>
    intro x y h
    obtain ⟨c, h1, h2⟩ := (mul_apply V W x y).1 h
    exact (hV x c h1).trans (hW c y h2)

end Defs

section Classes

variable {Q : Type*} {E : BRel Q}

/-- The union `⋃_{i ∈ I} β_i` of the rows of a set of classes `I`. -/
def betaUnion (hE : E * E = E) (I : Set (Cls E hE)) : Set Q := {k | ∃ i ∈ I, beta hE i k}

/-- The set of classes hit by the support `S` (the upper set of `S·E`). -/
def hitSet (hE : E * E = E) (S : Set Q) : Set (Cls E hE) := {i | ∃ s ∈ S, Hits hE s i}

/-- The set of classes hit is an upper set. -/
theorem hitSet_isUpperSet (hE : E * E = E) (S : Set Q) : IsUpperSet (hitSet hE S) := by
  rintro i j hij ⟨s, hs, k, hk, rfl, hsk⟩
  obtain ⟨k', hk', rfl⟩ := cls_surj hE j
  exact ⟨s, hs, k', hk', rfl, trans_of_idem hE hsk ((cls_le_cls hE hk hk').1 hij)⟩

/-- **The support at the end of an occurrence**: `S·E = ⋃_{i ∈ I} β_i`, where `I` is the set of classes hit by `S` (an upper set). -/
theorem act_E_eq_betaUnion [Finite Q] (hE : E * E = E) (S : Set Q) :
    act S E = betaUnion hE (hitSet hE S) := by
  ext b
  simp only [mem_act, betaUnion, hitSet]
  constructor
  · rintro ⟨s, hs, hsb⟩
    obtain ⟨i, hi, hb⟩ := (row_eq_union hE s b).1 hsb
    exact ⟨i, ⟨s, hs, hi⟩, hb⟩
  · rintro ⟨i, ⟨s, hs, hi⟩, hb⟩
    exact ⟨s, hs, (row_eq_union hE s b).2 ⟨i, hi, hb⟩⟩

/-- For an upper set `I`, an index `k` of `C_E` lies in `⋃_{i∈I} β_i` iff `[k] ∈ I`. -/
theorem mem_betaUnion_of_C (hE : E * E = E) {I : Set (Cls E hE)} (hI : IsUpperSet I) {k : Q}
    (hk : E k k) : k ∈ betaUnion hE I ↔ cls hE k hk ∈ I := by
  constructor
  · rintro ⟨i, hi, hik⟩
    exact hI ((beta_mem_C hE i k hk).1 hik) hi
  · intro h
    exact ⟨_, h, (beta_mem_C hE _ k hk).2 le_rfl⟩

/-- The upper set of a support is determined by the support: for upper sets `I, I'`, `⋃_I β = ⋃_{I'} β` implies `I = I'`. -/
theorem upperSet_unique (hE : E * E = E) {I I' : Set (Cls E hE)} (hI : IsUpperSet I)
    (hI' : IsUpperSet I') (h : betaUnion hE I = betaUnion hE I') : I = I' := by
  ext j
  obtain ⟨k, hk, rfl⟩ := cls_surj hE j
  rw [← mem_betaUnion_of_C hE hI hk, ← mem_betaUnion_of_C hE hI' hk, h]

end Classes

/-! ## 2. The permutation `π_X` of `X ∈ M` -/

section Pi

variable {Q : Type*} {E : BRel Q}

/-- The permutation `π_X` of `X`: the choice from `perm_of_inH` if `E X E ∈ 𝒢_E`, the identity otherwise. -/
noncomputable def piX (hE : E * E = E) (X : BRel Q) : Cls E hE ≃o Cls E hE := by
  classical
  exact if h : InH E (E * X * E) then Classical.choose (perm_of_inH hE h) else OrderIso.refl _

theorem piX_spec (hE : E * E = E) {X : BRel Q} (hX : InH E (E * X * E)) :
    ∀ q (hq : E q q), (E * X * E) q = beta hE (piX hE X (cls hE q hq)) := by
  classical
  have h : piX hE X = Classical.choose (perm_of_inH hE hX) := by
    simp only [piX, hX, ↓reduceDIte]
  rw [h]
  exact Classical.choose_spec (perm_of_inH hE hX)

/-- `π_X` is unique with the property `(E X E)_q = β_{π [q]}` (it agrees with every choice from `perm_of_inH`). -/
theorem piX_unique (hE : E * E = E) {X : BRel Q} (hX : InH E (E * X * E))
    {π : Cls E hE → Cls E hE} (hπ : ∀ q (hq : E q q), (E * X * E) q = beta hE (π (cls hE q hq))) :
    π = piX hE X :=
  perm_unique hE hπ (piX_spec hE hX)

/-- Transport of one class: `β_i · (X E) = β_{π_X(i)}`. -/
theorem act_beta (hE : E * E = E) {X : BRel Q} (hX : InH E (E * X * E)) (i : Cls E hE) (b : Q) :
    (∃ k, beta hE i k ∧ (X * E) k b) ↔ beta hE (piX hE X i) b := by
  obtain ⟨q, hq, rfl⟩ := cls_surj hE i
  rw [← piX_spec hE hX q hq, beta_cls, mul_assoc E X E, mul_apply]

/-- **Lemma 6.3 (iii) (one step)**: if `k ∈ β_j`, then `k · (X E) ⊆ β_{π_X(j)}`. -/
theorem carry_one (hE : E * E = E) {X : BRel Q} (hX : InH E (E * X * E)) {j : Cls E hE} {k : Q}
    (hk : beta hE j k) {b : Q} (hb : (X * E) k b) : beta hE (piX hE X j) b :=
  (act_beta hE hX j b).1 ⟨k, hk, hb⟩

/-- **Lemma 6.3 (i) (one step)**: `(⋃_{i∈I} β_i)·X·E = ⋃_{i∈I} β_{π_X(i)}` (`I` arbitrary). -/
theorem act_betaUnion (hE : E * E = E) {X : BRel Q} (hX : InH E (E * X * E))
    (I : Set (Cls E hE)) : act (act (betaUnion hE I) X) E = betaUnion hE (piX hE X '' I) := by
  rw [act_mul]
  ext b
  simp only [mem_act, betaUnion, Set.mem_image]
  constructor
  · rintro ⟨k, ⟨i, hi, hik⟩, hkb⟩
    exact ⟨_, ⟨i, hi, rfl⟩, carry_one hE hX hik hkb⟩
  · rintro ⟨_, ⟨i, hi, rfl⟩, hb⟩
    obtain ⟨k, hik, hkb⟩ := (act_beta hE hX i b).2 hb
    exact ⟨k, ⟨i, hi, hik⟩, hkb⟩

/-- An order automorphism maps upper sets to upper sets. -/
theorem piX_isUpperSet (hE : E * E = E) (X : BRel Q) {I : Set (Cls E hE)} (hI : IsUpperSet I) :
    IsUpperSet (piX hE X '' I) :=
  hI.image (piX hE X)

end Pi

/-! ## 3. Components: `C(π_X(j)) = C(j)` -/

section Comp

variable {Q : Type*} {B₀ B₁ E : BRel Q}

/-- The component `C(j)` of a class `j`: the set of indices mutually reachable with some index of `Q_j`. -/
def comp (B₀ B₁ : BRel Q) (hE : E * E = E) (j : Cls E hE) : Set Q :=
  {a | ∃ q hq, cls hE q hq = j ∧ Reach B₀ B₁ a q ∧ Reach B₀ B₁ q a}

/-- Indices of the same class are mutually reachable (`E ∈ M`). -/
theorem reach_of_cls_eq (hE : E * E = E) (hEM : E ∈ Mon B₀ B₁) {q q' : Q} (hq : E q q)
    (hq' : E q' q') (h : cls hE q hq = cls hE q' hq') : Reach B₀ B₁ q q' := by
  exact reach_of_mem hEM q q' ((cls_eq_cls hE hq hq').1 h).1

/-- Membership in `C(j)` can be decided with any representative. -/
theorem mem_comp_iff (hE : E * E = E) (hEM : E ∈ Mon B₀ B₁) {q : Q} (hq : E q q) (a : Q) :
    a ∈ comp B₀ B₁ hE (cls hE q hq) ↔ Reach B₀ B₁ a q ∧ Reach B₀ B₁ q a := by
  constructor
  · rintro ⟨q', hq', heq, h1, h2⟩
    exact ⟨h1.trans (reach_of_cls_eq hE hEM hq' hq heq),
      (reach_of_cls_eq hE hEM hq hq' heq.symm).trans h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨q, hq, rfl, h1, h2⟩

/-- **The core of Lemma 6.3 (ii)**: if `π_X [q] = [q']`, then `q` and `q'` are mutually reachable
(`R q q'` for `R := E X E`, and `R^m = E` gives `k` with `R q k ∧ R^{m-1} k q`). -/
theorem reach_pi [Finite Q] (hE : E * E = E) (hEM : E ∈ Mon B₀ B₁) {X : BRel Q}
    (hXM : X ∈ Mon B₀ B₁) (hX : InH E (E * X * E)) {q q' : Q} (hq : E q q) (hq' : E q' q')
    (h : piX hE X (cls hE q hq) = cls hE q' hq') :
    Reach B₀ B₁ q q' ∧ Reach B₀ B₁ q' q := by
  have hRM : E * X * E ∈ Mon B₀ B₁ := Submonoid.mul_mem _ (Submonoid.mul_mem _ hEM hXM) hEM
  have hrow : (E * X * E) q = E q' := by rw [piX_spec hE hX q hq, h, beta_cls]
  refine ⟨reach_of_mem hRM q q' (by rw [hrow]; exact hq'), ?_⟩
  obtain ⟨m, hm, hmE⟩ := hX.exists_pow_eq hE
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hm
  rw [Nat.zero_add, pow_succ'] at hmE
  have hqq : (E * X * E * (E * X * E) ^ n) q q := by rw [hmE]; exact hq
  obtain ⟨k, hqk, hkq⟩ := (mul_apply _ _ q q).1 hqq
  rw [hrow] at hqk
  exact (reach_of_mem hEM q' k hqk).trans
    (reach_of_mem (Submonoid.pow_mem _ hRM n) k q hkq)

/-- **Lemma 6.3 (ii)**: `C(π_X(j)) = C(j)`. -/
theorem comp_piX [Finite Q] (hE : E * E = E) (hEM : E ∈ Mon B₀ B₁) {X : BRel Q}
    (hXM : X ∈ Mon B₀ B₁) (hX : InH E (E * X * E)) (j : Cls E hE) :
    comp B₀ B₁ hE (piX hE X j) = comp B₀ B₁ hE j := by
  obtain ⟨q, hq, rfl⟩ := cls_surj hE j
  obtain ⟨q', hq', hq'eq⟩ := cls_surj hE (piX hE X (cls hE q hq))
  obtain ⟨h1, h2⟩ := reach_pi hE hEM hXM hX hq hq' hq'eq.symm
  ext a
  rw [← hq'eq, mem_comp_iff hE hEM hq' a, mem_comp_iff hE hEM hq a]
  exact ⟨fun ⟨ha1, ha2⟩ => ⟨ha1.trans h2, h1.trans ha2⟩,
    fun ⟨ha1, ha2⟩ => ⟨ha1.trans h1, h2.trans ha2⟩⟩

end Comp

end Collatz.Arctic.MinIdeal
