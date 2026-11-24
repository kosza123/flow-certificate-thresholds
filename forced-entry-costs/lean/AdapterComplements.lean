import AdapterMain

/-!
# Complements to the adapter theorem

* `walk_ext` : in an acyclic graph a path is determined by its set of arcs;
* `designated_ext` : a designated permutation that selects the return entry is determined by
  its set of used arcs;
* `route_of_path_unique`, `path_of_route_unique` : hence "the route uses exactly the arcs of the
  path" is a **bijection** between the paths from `s` to `t` of the original graph and the
  designated permutations that select the return entry (each path has exactly one such
  permutation, each such permutation has exactly one path);
* `dot_one` : the value of the identity matrix is the cost of the identity permutation;
* `dualRow_affine` : the row prices of the dual certificate are
  `dualRow θ x = ∑ over incidences p of θ j · [x = uRow p = uCol p]`, i.e. `θ j` at the first
  vertex of the B-feature of `j` and `0` elsewhere; in particular they are linear in `θ`.
-/

namespace DagCycleAssignment

open Finset

namespace Subdivision

variable {V A : Type*}

/-- **A path is determined by its set of arcs** (in an acyclic graph). -/
theorem walk_ext (tail head : A → V) {N : ℕ} (rank : V → Fin N)
    (hA : ∀ a, rank (tail a) < rank (head a)) {t : V} :
    ∀ (l l' : List A) (u : V), IsWalk tail head u t l → IsWalk tail head u t l' →
      (∀ a, a ∈ l ↔ a ∈ l') → l = l' := by
  intro l
  induction l with
  | nil =>
      intro l' u _ _ h
      cases l' with
      | nil => rfl
      | cons b l'' => exact absurd ((h b).2 List.mem_cons_self) (by simp)
  | cons a l1 ih =>
      intro l' u W W' h
      cases l' with
      | nil => exact absurd ((h a).1 List.mem_cons_self) (by simp)
      | cons a' l1' =>
          obtain ⟨h0, W1⟩ := W
          obtain ⟨h0', W1'⟩ := W'
          have haa : a = a' :=
            walk_tail_inj tail head rank hA (a' :: l1') u ⟨h0', W1'⟩ a
              ((h a).1 List.mem_cons_self) a' List.mem_cons_self (h0.trans h0'.symm)
          subst haa
          have hnot : ∀ m : List A, IsWalk tail head (head a) t m → a ∉ m := by
            intro m Wm ham
            have h1 := ((walk_rank tail head rank hA m (head a) Wm).2 a ham).1
            exact absurd (lt_of_lt_of_le (hA a) h1) (lt_irrefl _)
          have hset : ∀ b, b ∈ l1 ↔ b ∈ l1' := by
            intro b
            constructor
            · intro hb
              rcases List.mem_cons.1 ((h b).1 (List.mem_cons_of_mem _ hb)) with hba | hb'
              · rw [hba] at hb
                exact absurd hb (hnot l1 W1)
              · exact hb'
            · intro hb
              rcases List.mem_cons.1 ((h b).2 (List.mem_cons_of_mem _ hb)) with hba | hb'
              · rw [hba] at hb
                exact absurd hb (hnot l1' W1')
              · exact hb'
          rw [ih l1' (head a) W1 W1' hset]

/-- **A route is determined by its set of used arcs.** -/
theorem designated_ext (tail head : A → V) (length : A → ℕ) {s t : V} (hst : s ≠ t)
    {σ σ' : Equiv.Perm (Vertex V A length)}
    (hσ : Designated (Edge tail head length) (Sum.inl s) (Sum.inl t) σ)
    (hσ' : Designated (Edge tail head length) (Sum.inl s) (Sum.inl t) σ')
    (hret : σ (Sum.inl t) = Sum.inl s) (hret' : σ' (Sum.inl t) = Sum.inl s)
    (h : ∀ a, Used tail length σ a ↔ Used tail length σ' a) : σ = σ' := by
  apply Equiv.ext
  intro x
  rcases x with v | ⟨a, i⟩
  · rcases hσ (Sum.inl v) with hfix | hedge | hr
    · rcases hσ' (Sum.inl v) with hfix' | hedge' | hr'
      · rw [hfix, hfix']
      · exfalso
        obtain ⟨b, hvb, hy⟩ := edge_from_original tail head length hedge' v rfl
        have hU' : Used tail length σ' b := by
          unfold Used
          rw [← hvb]
          exact hy
        have hU := (h b).2 hU'
        unfold Used at hU
        rw [← hvb, hfix] at hU
        cases hU
      · exfalso
        have hv : v = t := Sum.inl.inj hr'.1
        rw [hv, hret] at hfix
        exact hst (Sum.inl.inj hfix)
    · obtain ⟨b, hvb, hy⟩ := edge_from_original tail head length hedge v rfl
      have hU : Used tail length σ b := by
        unfold Used
        rw [← hvb]
        exact hy
      have hU' := (h b).1 hU
      unfold Used at hU'
      rw [← hvb] at hU'
      rw [hy, hU']
    · have hv : v = t := Sum.inl.inj hr.1
      rw [hv, hret, hret']
  · show σ (internal length a i) = σ' (internal length a i)
    by_cases hm : σ (internal length a i) = internal length a i
    · have hnU : ¬ Used tail length σ a := by
        intro hU
        obtain ⟨j, hj⟩ := (chain_entry_iff_any_internal_moved tail head length hσ a).mp hU
        exact (whole_chain_forced tail head length hσ a j hj).2.2.2 i hm
      have hfix' : σ' (internal length a i) = internal length a i := by
        by_contra hm'
        exact hnU ((h a).2
          ((chain_entry_iff_any_internal_moved tail head length hσ' a).mpr ⟨i, hm'⟩))
      rw [hm, hfix']
    · have hU : Used tail length σ a :=
        (chain_entry_iff_any_internal_moved tail head length hσ a).mpr ⟨i, hm⟩
      obtain ⟨j, hj⟩ :=
        (chain_entry_iff_any_internal_moved tail head length hσ' a).mp ((h a).1 hU)
      have hm' : σ' (internal length a i) ≠ internal length a i :=
        (whole_chain_forced tail head length hσ' a j hj).2.2.2 i
      rw [moved_internal_outgoing tail head length hσ a i hm,
        moved_internal_outgoing tail head length hσ' a i hm']

/-- **Bijection, first half.**  A path of the original graph has exactly one route that uses
exactly its arcs. -/
theorem route_of_path_unique [DecidableEq V] [DecidableEq A] (tail head : A → V)
    (length : A → ℕ) {s t : V} {N : ℕ} (rank : V → Fin N)
    (hA : ∀ a, rank (tail a) < rank (head a)) (hst : s ≠ t) {l : List A}
    (W : IsWalk tail head s t l) :
    ∃! σ : Equiv.Perm (Vertex V A length),
      Designated (Edge tail head length) (Sum.inl s) (Sum.inl t) σ ∧
      σ (Sum.inl t) = Sum.inl s ∧ ∀ a, Used tail length σ a ↔ a ∈ l := by
  obtain ⟨σ, hσ, hret, hU⟩ := exists_designated_of_walk tail head length s t l rank hA hst W
  refine ⟨σ, ⟨hσ, hret, hU⟩, ?_⟩
  rintro σ' ⟨hσ', hret', hU'⟩
  exact designated_ext tail head length hst hσ' hσ hret' hret
    (fun a => (hU' a).trans (hU a).symm)

/-- **Bijection, second half.**  A route has exactly one path of the original graph whose arcs
are exactly its used arcs. -/
theorem path_of_route_unique (tail head : A → V) (length : A → ℕ) {s t : V} {N : ℕ}
    (rank : V → Fin N) (hA : ∀ a, rank (tail a) < rank (head a)) (hst : s ≠ t)
    {σ : Equiv.Perm (Vertex V A length)}
    (hσ : Designated (Edge tail head length) (Sum.inl s) (Sum.inl t) σ)
    (hret : σ (Sum.inl t) = Sum.inl s) :
    ∃! l : List A, IsWalk tail head s t l ∧ ∀ a, a ∈ l ↔ Used tail length σ a := by
  obtain ⟨l, hl, hU⟩ := walk_of_designated tail head length rank hA hst hσ hret
  refine ⟨l, ⟨hl, hU⟩, ?_⟩
  rintro l' ⟨hl', hU'⟩
  exact walk_ext tail head rank hA l' l s hl' hl (fun a => (hU' a).trans (hU a).symm)

end Subdivision

namespace Adapter

open Subdivision

/-- The value of the identity matrix is the cost of the identity permutation. -/
theorem dot_one {n : Type*} [Fintype n] [DecidableEq n] (C : n → n → ℝ) :
    dot C (1 : Matrix n n ℝ) = ∑ x, C x x := by
  rw [← permMatrix_refl, dot_permMatrix]
  rfl

variable {V A J : Type*} [DecidableEq A] [Fintype J] [DecidableEq V]

/-- **The dual row prices are linear in the scenario**: `θ j` at the first vertex of the
B-feature of `j`, `0` at every other vertex. -/
theorem dualRow_affine (arcA arcB : J → A) (θ : J → ℝ)
    (x : Vertex V A (chainLength arcA arcB)) :
    dualRow arcA arcB θ x
      = ∑ p : Incidence J,
          θ p.1 * (if x = uRow V arcA arcB p ∧ x = uCol V arcA arcB p then 1 else 0) := by
  rcases x with u | ⟨a, i⟩
  · have h0 : dualRow arcA arcB θ (Sum.inl u : Vertex V A (chainLength arcA arcB)) = 0 := rfl
    rw [h0]
    symm
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [if_neg, mul_zero]
    rintro ⟨h, _⟩
    cases h
  · show diagCost arcA arcB θ a i.val
      = ∑ p : Incidence J, θ p.1 *
          (if (internal (chainLength arcA arcB) a i : Vertex V A (chainLength arcA arcB))
                = uRow V arcA arcB p
              ∧ (internal (chainLength arcA arcB) a i : Vertex V A (chainLength arcA arcB))
                = uCol V arcA arcB p then 1 else 0)
    have hcond : ∀ p : Incidence J,
        ((internal (chainLength arcA arcB) a i : Vertex V A (chainLength arcA arcB))
              = uRow V arcA arcB p
            ∧ (internal (chainLength arcA arcB) a i : Vertex V A (chainLength arcA arcB))
              = uCol V arcA arcB p) ↔
          ((internal (chainLength arcA arcB) a i : Vertex V A (chainLength arcA arcB))
              = firstV V arcA arcB p ∧ p.2 = false) := by
      intro p
      refine (uEntry_iff V arcA arcB a a i i p).trans ⟨?_, ?_⟩
      · rintro ⟨h1, _, ⟨_, h⟩ | ⟨h, _⟩⟩
        · omega
        · exact ⟨h1, h⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, rfl, Or.inr ⟨h2, rfl⟩⟩
    simp only [hcond]
    have hterm : ∀ p : Incidence J, θ p.1 *
        (if (internal (chainLength arcA arcB) a i : Vertex V A (chainLength arcA arcB))
              = firstV V arcA arcB p ∧ p.2 = false
          then (1 : ℝ) else 0)
        = featureDiag θ p *
          (if (internal (chainLength arcA arcB) a i : Vertex V A (chainLength arcA arcB))
              = firstV V arcA arcB p then 1 else 0) := by
      intro p
      by_cases hF : (internal (chainLength arcA arcB) a i :
          Vertex V A (chainLength arcA arcB)) = firstV V arcA arcB p <;>
        by_cases hp : p.2 = true <;> simp [featureDiag, hF, hp]
    rw [Finset.sum_congr rfl (fun p _ => hterm p), sum_firstV V arcA arcB (featureDiag θ) a i]
    rfl

end Adapter
end DagCycleAssignment
