import Kenyon.Forest

/-!
# Three examples

A check that `numTrees` counts what it should on three small multigraphs:

* `numTrees_loop`  : one vertex with one loop has exactly one spanning tree (the empty set);
* `numTrees_digon` : two vertices joined by two parallel edges have exactly two spanning trees;
* `numTrees_K4`    : the complete graph `K₄` (edges `01, 02, 03, 12, 13, 23`) has `16 = 4²`
  spanning trees (Cayley).  Proof: an edge set is a spanning tree iff it has three edges and
  three rounds of "add the far ends of edges at reached vertices" reach every vertex from `0`
  (the reached set is closed, so a missed vertex cannot be joined to `0`, by `exists_crossing`);
  the 64 edge sets are then counted by `decide`.
-/

open Finset

namespace Kenyon

theorem numTrees_loop : numTrees (fun _ : Unit => ()) (fun _ : Unit => ()) = 1 := by
  classical
  unfold numTrees
  have h : ((univ : Finset (Finset Unit)).filter
      fun T => IsTree (fun _ : Unit => ()) (fun _ : Unit => ()) T) = {∅} := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hT
      have h1 := hT.1
      rw [Fintype.card_unit] at h1
      exact Finset.card_eq_zero.1 (by omega)
    · rintro rfl
      exact ⟨by simp, fun x y => by cases x; cases y; exact Relation.ReflTransGen.refl⟩
  rw [h, Finset.card_singleton]

theorem numTrees_digon :
    numTrees (fun _ : Fin 2 => (0 : Fin 2)) (fun _ : Fin 2 => (1 : Fin 2)) = 2 := by
  classical
  unfold numTrees
  have h : ((univ : Finset (Finset (Fin 2))).filter
      fun T => IsTree (fun _ : Fin 2 => (0 : Fin 2)) (fun _ : Fin 2 => (1 : Fin 2)) T)
      = Finset.powersetCard 1 univ := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
      Finset.subset_univ]
    constructor
    · intro hT
      have h1 := hT.1
      rw [Fintype.card_fin] at h1
      omega
    · intro hT
      obtain ⟨e, rfl⟩ := Finset.card_eq_one.1 hT
      have h01 : Conn (fun _ : Fin 2 => (0 : Fin 2)) (fun _ : Fin 2 => (1 : Fin 2)) {e} 0 1 :=
        Relation.ReflTransGen.single ⟨e, Finset.mem_singleton_self e, Or.inl ⟨rfl, rfl⟩⟩
      refine ⟨by simp, fun x y => ?_⟩
      fin_cases x <;> fin_cases y
      · exact Relation.ReflTransGen.refl
      · exact h01
      · exact h01.symm
      · exact Relation.ReflTransGen.refl
  rw [h, Finset.card_powersetCard]
  simp

section K4

/-- Tails of the edges `01, 02, 03, 12, 13, 23` of `K₄`. -/
def k4Src : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]
/-- Heads of the edges of `K₄`. -/
def k4Tgt : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

/-- One round of reachability: add the other ends of the edges of `T` at reached vertices. -/
def k4Step (T : Finset (Fin 6)) (R : Finset (Fin 4)) : Finset (Fin 4) :=
  R ∪ (T.filter fun e => k4Src e ∈ R).image k4Tgt ∪ (T.filter fun e => k4Tgt e ∈ R).image k4Src

/-- The vertices reached from `0` in three rounds. -/
def k4Reach (T : Finset (Fin 6)) : Finset (Fin 4) := k4Step T (k4Step T (k4Step T {0}))

theorem k4Step_conn {T : Finset (Fin 6)} {R : Finset (Fin 4)}
    (hR : ∀ w ∈ R, Conn k4Src k4Tgt T 0 w) : ∀ w ∈ k4Step T R, Conn k4Src k4Tgt T 0 w := by
  intro w hw
  simp only [k4Step, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hw
  rcases hw with (hw | ⟨e, ⟨he, hs⟩, rfl⟩) | ⟨e, ⟨he, ht⟩, rfl⟩
  · exact hR w hw
  · exact (hR _ hs).tail ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
  · exact (hR _ ht).tail ⟨e, he, Or.inr ⟨rfl, rfl⟩⟩

theorem k4Reach_conn {T : Finset (Fin 6)} : ∀ w ∈ k4Reach T, Conn k4Src k4Tgt T 0 w := by
  unfold k4Reach
  refine k4Step_conn (k4Step_conn (k4Step_conn fun w hw => ?_))
  rw [Finset.mem_singleton.1 hw]
  exact Relation.ReflTransGen.refl

/-- The reached set is closed under the edges of `T` (a finite check). -/
theorem k4Reach_closed : ∀ T : Finset (Fin 6), ∀ e ∈ T,
    (k4Src e ∈ k4Reach T → k4Tgt e ∈ k4Reach T) ∧ (k4Tgt e ∈ k4Reach T → k4Src e ∈ k4Reach T) := by
  decide

theorem k4_isTree_iff (T : Finset (Fin 6)) :
    IsTree k4Src k4Tgt T ↔ T.card = 3 ∧ k4Reach T = Finset.univ := by
  constructor
  · intro hT
    have h1 := hT.1
    rw [Fintype.card_fin] at h1
    refine ⟨by omega, ?_⟩
    by_contra hne
    obtain ⟨w, hw⟩ : ∃ w, w ∉ k4Reach T := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hne (Finset.eq_univ_iff_forall.2 h)
    have h0 : (0 : Fin 4) ∈ k4Reach T := by unfold k4Reach k4Step; simp
    obtain ⟨e, he, hcr⟩ := exists_crossing (hT.2 w 0) hw h0
    rcases hcr with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · exact hs ((k4Reach_closed T e he).2 ht)
    · exact ht ((k4Reach_closed T e he).1 hs)
  · rintro ⟨hc, hR⟩
    refine ⟨by rw [hc, Fintype.card_fin], fun x y => ?_⟩
    have hx := k4Reach_conn x (hR ▸ Finset.mem_univ x)
    have hy := k4Reach_conn y (hR ▸ Finset.mem_univ y)
    exact hx.symm.trans hy

/-- **`K₄` has `16` spanning trees.** -/
theorem numTrees_K4 :
    numTrees (![0, 0, 0, 1, 1, 2] : Fin 6 → Fin 4) (![1, 2, 3, 2, 3, 3] : Fin 6 → Fin 4) = 16 := by
  classical
  show numTrees k4Src k4Tgt = 16
  unfold numTrees
  have h : ((univ : Finset (Finset (Fin 6))).filter fun T => IsTree k4Src k4Tgt T)
      = (univ : Finset (Finset (Fin 6))).filter fun T => T.card = 3 ∧ k4Reach T = Finset.univ := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact k4_isTree_iff T
  rw [h]
  decide

end K4

end Kenyon
