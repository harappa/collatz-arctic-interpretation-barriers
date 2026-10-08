/-
General form of the bridge to the systems.

With the map `f`, the domain `dom`, the rules `rules` and the canonical derivation `cd` as arguments, the part deriving the arctic barrier from the general `AutoCoreG`
is written only once. The checked files for $T$ are not changed; the following are copied and generalized (the proofs are the same as in the source).

* `Chain.append`, `DChain.append`: concatenation of chains (absent for $T$; a step $\mathsf b$ of $H$ consists of two consecutive sweeps).
* `sweepRules_memG`: `Main.sweepRules_mem` with the set of rules as an argument.
* `orbit_boundG` (`Main.orbit_bound`) and `barrier_of_autoCoreG` (combining `Main.arctic_barrier_ST` and
  `AutoBridge.valueCore_of_autoCore`): the general form of Theorem 3.1 (rule removal).
* `orbit_chainG` (`DPBridge.orbit_chain`), `barrier_of_auto_arcG` (`DPMain.barrier_of_auto_arc`),
  `barrier_of_auto_arcZG` (`BZShift.barrier_of_auto_arcZ`, the translation of Lemma 5.3): the value part of Theorems 3.3 and 3.4.
  Besides `AutoCore`, `barrier_of_auto_arc(Z)` for $T$ uses only the finiteness of values at all `n` and the estimate of steps
  at points of the domain, so it generalizes as it is, with the map, the domain and the canonical derivation as arguments.
* `dsweepG`, `dsweep_revG` (`DPCanon.dsweep`, `dsweep_rev` with the usable rules `U` and the root rules `P` as arguments) are
  split off into `Gen/SysSweep.lean` because of the limit of 20 KB per file.

The lemmas on the number of uses `usesOrbitG_zero`, `usesOrbitG_succ` are `private` to avoid clashes with lemmas of the same name in other files.
-/
import CollatzProof.Arctic.Gen.Model
import CollatzProof.Arctic.AutoBridge
import CollatzProof.Arctic.DPMain
import CollatzProof.Arctic.BZMain

namespace Collatz.Arctic.Gen

open Collatz.Arctic Matrix

/-! ## Concatenation of chains, and membership of the rules of sweeps -/

/-- Concatenation of derivations by lists of rules. -/
theorem Chain.append {rs₁ rs₂ : List Rule} {u w v : Word} (h₁ : Chain rs₁ u w)
    (h₂ : Chain rs₂ w v) : Chain (rs₁ ++ rs₂) u v := by
  induction h₁ with
  | nil u => simpa using h₂
  | cons hs _ ih => exact Chain.cons hs (ih h₂)

/-- Concatenation of chains of dependency pairs. -/
theorem DChain.append {U P rs₁ rs₂ : List Rule} {u w v : Word} (h₁ : DChain U P rs₁ u w)
    (h₂ : DChain U P rs₂ w v) : DChain U P (rs₁ ++ rs₂) u v := by
  induction h₁ with
  | nil _ => simpa using h₂
  | under hρ hs _ ih => exact DChain.under hρ hs (ih h₂)
  | root q hρ _ ih => exact DChain.root q hρ (ih h₂)

/-- The rules used in a sweep belong to any set `S` containing the carry rules and the left-end rules (the general form of `Main.sweepRules_mem`). -/
theorem sweepRules_memG {S : List Rule} (hA : ∀ b d, b < 2 → d ≤ 2 → aRule b d ∈ S)
    (hL : ∀ d, d ≤ 2 → leftRule d ∈ S) :
    ∀ (bs : List ℕ) (d : ℕ), (∀ b ∈ bs, b < 2) → d ≤ 2 → ∀ σ ∈ sweepRules bs d, σ ∈ S
  | [], d, _, hd => by
    intro σ hσ
    simp only [sweepRules, List.mem_singleton] at hσ
    subst hσ
    exact hL d hd
  | b :: bs, d, hbs, hd => by
    intro σ hσ
    simp only [sweepRules, List.mem_cons] at hσ
    have hb : b < 2 := hbs b List.mem_cons_self
    rcases hσ with rfl | hσ
    · exact hA b d hb hd
    · exact sweepRules_memG hA hL bs _ (fun b' hb' => hbs b' (List.mem_cons_of_mem _ hb'))
        (by omega) σ hσ

/-! ## Rule removal (the general form of Theorem 3.1) -/

private theorem usesOrbitG_zero (f : ℕ → ℕ) (cd : ℕ → List Rule) (ρ : Rule) (n : ℕ) :
    usesOrbitG f cd ρ n 0 = 0 := by
  simp [usesOrbitG]

private theorem usesOrbitG_succ (f : ℕ → ℕ) (cd : ℕ → List Rule) (ρ : Rule) (n m : ℕ) :
    usesOrbitG f cd ρ n (m + 1) = (cd n).count ρ + usesOrbitG f cd ρ (f n) m := by
  simp only [usesOrbitG, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  congr 2

/-- Estimate along the orbit (the general form of `Main.orbit_bound`): `Φ` decreases by the number of uses of the strictly oriented rule `ρ`. -/
theorem orbit_boundG {f : ℕ → ℕ} {dom : ℕ → Prop} {rules : List Rule} {cd : ℕ → List Rule}
    (hchain : ∀ n, dom n → Chain (cd n) (can n) (can (f n)))
    (hsub : ∀ n, dom n → ∀ σ ∈ cd n, σ ∈ rules)
    {d : ℕ} (hd : 0 < d) (I : Interp d) (hfin : Fin00 hd I)
    (hweak : ∀ ρ ∈ rules, Weak I ρ) {ρ : Rule} (hρ : Strict I ρ) :
    ∀ (m n : ℕ), (∀ i < m, dom (f^[i] n)) → ∀ a b : ℕ, Phi hd I (can n) = Arc.fin a →
      Phi hd I (can (f^[m] n)) = Arc.fin b → b + usesOrbitG f cd ρ n m ≤ a := by
  intro m
  induction m with
  | zero =>
    intro n _ a b ha hb
    simp only [Function.iterate_zero, id] at hb
    rw [ha] at hb
    have hab : a = b := Arc.fin_inj hb
    simp [usesOrbitG_zero, hab]
  | succ m ih =>
    intro n horb a b ha hb
    have hn : dom n := by simpa using horb 0 (Nat.succ_pos m)
    obtain ⟨c, hc⟩ := phi_fin hd I hfin (can (f n))
    have hstep := phi_chain hd I hfin hρ (hchain n hn)
      (fun σ hσ => hweak σ (hsub n hn σ hσ)) a c ha hc
    have horb' : ∀ i < m, dom (f^[i] (f n)) := by
      intro i hi
      have := horb (i + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    have hb' : Phi hd I (can (f^[m] (f n))) = Arc.fin b := by
      rwa [← Function.iterate_succ_apply]
    have hrest := ih (f n) horb' c b hc hb'
    rw [usesOrbitG_succ]
    omega

/-- **General form of rule removal**: from `AutoCoreG` and from the correctness of the canonical derivation and the membership of its rules at points of the domain, an arctic interpretation
(of any dimension) that weakly orients all rules and has all `(M_s)₀₀` finite strictly orients no rule. -/
theorem barrier_of_autoCoreG {f : ℕ → ℕ} {dom : ℕ → Prop} {rules : List Rule} {cd : ℕ → List Rule}
    (h : AutoCoreG f dom rules cd)
    (hchain : ∀ n, dom n → Chain (cd n) (can n) (can (f n)))
    (hsub : ∀ n, dom n → ∀ σ ∈ cd n, σ ∈ rules) :
    ∀ (d : ℕ) (hd : 0 < d) (I : Interp d), Fin00 hd I → (∀ ρ ∈ rules, Weak I ρ) →
      ∀ ρ ∈ rules, ¬ Strict I ρ := by
  intro d hd I hfin hweak ρ hρmem hρ
  have hval := phi_can_eq_autoVal hd I
  obtain ⟨n, -, m, horb, hlt⟩ := h d (fun j => I Letter.lft ⟨0, hd⟩ j) I
    (fun j => I Letter.rgt j ⟨0, hd⟩) 0
    (by
      intro n _ h0
      rw [← hval] at h0
      exact phi_finite hd I hfin (can n) (by rw [h0]; rfl))
    (by
      intro n hn a b ha hb
      rw [← hval] at ha hb
      have := phi_chain_weak hd I (hchain n hn) (fun σ hσ => hweak σ (hsub n hn σ hσ))
      rw [ha, hb, Arc.fin_le_fin] at this
      omega)
    ρ hρmem 0
  rw [← hval] at hlt
  obtain ⟨a, ha⟩ := phi_fin hd I hfin (can n)
  obtain ⟨b, hb⟩ := phi_fin hd I hfin (can (f^[m] n))
  have hbound := orbit_boundG hchain hsub hd I hfin hweak hρ m n horb a b ha hb
  rw [ha, Arc.fin_lt_fin] at hlt
  omega

/-! ## The value part of dependency pairs and below zero (the general form of Theorems 3.3 and 3.4) -/

/-- Estimate along the orbit (the general form of `DPBridge.orbit_chain`). -/
theorem orbit_chainG {R : Type} [CommSemiring R] [LinearOrder R] [ArcticOrder R]
    (f : ℕ → ℕ) (dom : ℕ → Prop) (cd : ℕ → List Rule) (V : ℕ → R) (e : R) (σ : Rule)
    (hstep : ∀ n, dom n → V (f n) * e ^ ((cd n).count σ) ≤ V n) :
    ∀ m n, (∀ i < m, dom (f^[i] n)) → V (f^[m] n) * e ^ (usesOrbitG f cd σ n m) ≤ V n := by
  intro m
  induction m with
  | zero => intro n _; simp [usesOrbitG_zero]
  | succ m ih =>
    intro n horb
    have hn : dom n := by simpa using horb 0 (Nat.succ_pos m)
    have horb' : ∀ i < m, dom (f^[i] (f n)) := by
      intro i hi
      have := horb (i + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    rw [Function.iterate_succ_apply, usesOrbitG_succ, pow_add, mul_comm (e ^ _), ← mul_assoc]
    exact (ArcticOrder.mul_mono (ih (f n) horb') le_rfl).trans (hstep n hn)

/-- The value barrier for `𝔸_ℕ` (the general form of `DPMain.barrier_of_auto_arc`): if the value is finite at all `n` and decreases, at steps from points of the domain,
by the number of uses of the strictly oriented rule `σ`, this contradicts `AutoCoreG` (`κ = 0`). -/
theorem barrier_of_auto_arcG {f : ℕ → ℕ} {dom : ℕ → Prop} {rules : List Rule}
    {cd : ℕ → List Rule} (hcore : AutoCoreG f dom rules cd) {D : ℕ} (u : Fin D → Arc)
    (A : Interp D) (c : Fin D → Arc) (σ : Rule) (hσ : σ ∈ rules)
    (hfin : ∀ n, autoVal u A c n ≠ 0)
    (hstep : ∀ n, dom n →
      autoVal u A c (f n) * Arc.fin 1 ^ ((cd n).count σ) ≤ autoVal u A c n) :
    False := by
  have horb := orbit_chainG f dom cd (fun n => autoVal u A c n) (Arc.fin 1) σ hstep
  obtain ⟨n, -, m, hm, hlt⟩ := hcore D u A c 0 (fun n _ => hfin n)
    (by
      intro n hn a b ha hb
      have := hstep n hn
      rw [ha, hb, Arc.fin_one_pow, Arc.fin_mul_fin, Arc.fin_le_fin] at this
      omega)
    σ hσ 0
  -- contradiction between the conclusion `V(n) < number of uses` and the estimate along the orbit `V(f^m n) + number of uses ≤ V(n)`
  obtain ⟨a, ha⟩ := Arc.exists_fin_of_ne_zero (hfin n)
  obtain ⟨b, hb⟩ := Arc.exists_fin_of_ne_zero (hfin (f^[m] n))
  have := horb m n hm
  rw [ha, hb, Arc.fin_one_pow, Arc.fin_mul_fin, Arc.fin_le_fin] at this
  rw [ha, zero_mul, zero_add, Arc.fin_lt_fin] at hlt
  omega

/-- **General form of the barrier by translation** (`BZShift.barrier_of_auto_arcZ`; the translation of Lemma 5.3 is carried out in this proof): if, for an automaton with entries in `ℤ ∪ {−∞}`, the value is
a natural number and decreases, at steps from points of the domain, by the number of uses of the strictly oriented rule `σ`, this contradicts `AutoCoreG` (slope `κ = K`). -/
theorem barrier_of_auto_arcZG {f : ℕ → ℕ} {dom : ℕ → Prop} {rules : List Rule}
    {cd : ℕ → List Rule} (hcore : AutoCoreG f dom rules cd) {D : ℕ} (u : Fin D → ArcZ)
    (A : Letter → Matrix (Fin D) (Fin D) ArcZ) (c : Fin D → ArcZ) (σ : Rule) (hσ : σ ∈ rules)
    (hnn : ∀ n, ∃ z : ℕ, autoValZ u A c n = ArcZ.fin z)
    (hstep : ∀ n, dom n →
      autoValZ u A c (f n) * ArcZ.fin 1 ^ ((cd n).count σ) ≤ autoValZ u A c n) :
    False := by
  classical
  -- the amount of the translation
  set K : ℕ := ∑ i, ∑ j, (ArcZ.nb (A Letter.f i j) + ArcZ.nb (A Letter.t i j)) with hK
  set Ku : ℕ := ∑ i, ArcZ.nb (u i) with hKu
  set Kc : ℕ := ∑ i, ArcZ.nb (c i) with hKc
  have hKA : ∀ s, s = Letter.f ∨ s = Letter.t → ∀ i j, ArcZ.nb (A s i j) ≤ K := by
    intro s hs i j
    have h1 : ArcZ.nb (A s i j) ≤ ArcZ.nb (A Letter.f i j) + ArcZ.nb (A Letter.t i j) := by
      rcases hs with rfl | rfl <;> omega
    have h2 : ArcZ.nb (A Letter.f i j) + ArcZ.nb (A Letter.t i j) ≤
        ∑ j', (ArcZ.nb (A Letter.f i j') + ArcZ.nb (A Letter.t i j')) :=
      Finset.single_le_sum (f := fun j' => ArcZ.nb (A Letter.f i j') + ArcZ.nb (A Letter.t i j'))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have h3 : ∑ j', (ArcZ.nb (A Letter.f i j') + ArcZ.nb (A Letter.t i j')) ≤ K :=
      Finset.single_le_sum
        (f := fun i' => ∑ j', (ArcZ.nb (A Letter.f i' j') + ArcZ.nb (A Letter.t i' j')))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hKu' : ∀ i, ArcZ.nb (u i) ≤ Ku := fun i =>
    Finset.single_le_sum (f := fun i' => ArcZ.nb (u i')) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have hKc' : ∀ i, ArcZ.nb (c i) ≤ Kc := fun i =>
    Finset.single_le_sum (f := fun i' => ArcZ.nb (c i')) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  -- the translated automaton over `Arc`
  let u' : Fin D → Arc := fun i => ArcZ.toArc (ArcZ.fin Ku * u i)
  let A' : Interp D := fun s => Matrix.of fun i j => ArcZ.toArc (ArcZ.fin K * A s i j)
  let c' : Fin D → Arc := fun i => ArcZ.toArc (ArcZ.fin Kc * c i)
  have hu' : (ArcZ.ofArcHom ∘ u') = ArcZ.fin Ku • u := by
    funext i; exact ArcZ.ofArc_toArc_shift Ku (u i) (hKu' i)
  have hc' : (ArcZ.ofArcHom ∘ c') = ArcZ.fin Kc • c := by
    funext i; exact ArcZ.ofArc_toArc_shift Kc (c i) (hKc' i)
  have hA' : ∀ s, s = Letter.f ∨ s = Letter.t → (A' s).map ArcZ.ofArcHom = ArcZ.fin K • A s := by
    intro s hs; ext i j
    exact ArcZ.ofArc_toArc_shift K (A s i j) (hKA s hs i j)
  -- key: the translated value is `V(n) + K_u + K·lenT n + K_c` (all paths have length `lenT n`)
  have hkey : ∀ n, ArcZ.ofArcHom (autoVal u' A' c' n) =
      ArcZ.fin ((Ku + K * lenT n + Kc : ℕ) : ℤ) * autoValZ u A c n := by
    intro n
    have hprod :
        (ev A' (binTail n)).map ArcZ.ofArcHom = ArcZ.fin K ^ lenT n • evR A (binTail n) := by
      unfold ev
      rw [← RingHom.mapMatrix_apply, map_list_prod, List.map_map]
      rw [List.map_congr_left (g := fun s => ArcZ.fin K • A s)
        (fun s hs => by simpa using hA' s (binTail_letters n s hs))]
      exact prod_map_smul _ _ _
    unfold autoVal
    rw [RingHom.map_dotProduct, hu']
    have hmv : (ArcZ.ofArcHom ∘ (ev A' (binTail n) *ᵥ c')) =
        (ev A' (binTail n)).map ArcZ.ofArcHom *ᵥ (ArcZ.ofArcHom ∘ c') := by
      funext i; exact RingHom.map_mulVec _ _ _ i
    rw [hmv, hprod, hc', Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul,
      dotProduct_smul, smul_dotProduct, ArcZ.fin_pow]
    simp only [smul_eq_mul, autoValZ, ← mul_assoc, ArcZ.fin_mul_fin]
    congr 2
    push_cast; ring
  have hval : ∀ n (z : ℕ), autoValZ u A c n = ArcZ.fin z →
      autoVal u' A' c' n = Arc.fin (Ku + K * lenT n + Kc + z) := by
    intro n z hz
    apply ArcZ.ofArc_eq_fin
    have := hkey n
    rw [hz, ArcZ.fin_mul_fin] at this
    rw [← ArcZ.ofArcHom_apply, this]
    push_cast; rfl
  -- one-step estimate at points of the domain (in natural numbers)
  have hdrop : ∀ n, dom n → ∀ a b : ℕ, autoValZ u A c n = ArcZ.fin a →
      autoValZ u A c (f n) = ArcZ.fin b → b + (cd n).count σ ≤ a := by
    intro n hn a b ha hb
    have := hstep n hn
    rw [ha, hb, ArcZ.fin_pow, ArcZ.fin_mul_fin, ArcZ.fin_le_fin] at this
    omega
  -- apply `AutoCoreG` with slope `κ = K` (hypotheses: values are finite, and they do not increase faster than slope `K` at steps from the domain)
  obtain ⟨n, -, m, hm, hlt⟩ := hcore D u' A' c' K
    (by
      intro n _
      obtain ⟨z, hz⟩ := hnn n
      rw [hval n z hz]
      exact (Arc.ne_zero_iff _).mpr (by rw [Arc.val_fin]; exact WithBot.coe_ne_bot))
    (by
      intro n hn a b ha hb
      obtain ⟨z, hz⟩ := hnn n
      obtain ⟨z', hz'⟩ := hnn (f n)
      have h1 := hval n z hz
      have h2 := hval (f n) z' hz'
      rw [ha] at h1
      rw [hb] at h2
      have h1 := Arc.fin_inj h1
      have h2 := Arc.fin_inj h2
      have := hdrop n hn z z' hz hz'
      subst h1 h2
      omega)
    σ hσ 0
  -- contradiction between the conclusion `V(n) < number of uses` and the estimate along the orbit `V(f^m n) + number of uses ≤ V(n)`
  obtain ⟨z, hz⟩ := hnn n
  obtain ⟨z', hz'⟩ := hnn (f^[m] n)
  have horb := orbit_chainG f dom cd (fun n => autoValZ u A c n) (ArcZ.fin 1) σ hstep m n hm
  rw [hz, hz', ArcZ.fin_pow, ArcZ.fin_mul_fin, ArcZ.fin_le_fin] at horb
  rw [hval n z hz, Arc.fin_lt_fin] at hlt
  omega

end Collatz.Arctic.Gen
