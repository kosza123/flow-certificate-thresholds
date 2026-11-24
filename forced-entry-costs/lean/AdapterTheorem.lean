import AdapterBirkhoff
import AdapterPaths
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Fintype.Pi

/-!
# The adapter theorem: the forced value in terms of paths of the original graph

For a path `l` of the original graph (a list of arcs, `IsWalk tail head s t l`):

* `pathCost … θ l = ∑_{a ∈ l} α a + ∑ j, (θ j · [arcA j ∈ l] + (β j − θ j) · [arcB j ∈ l])`;
* `quadCost … l  = ∑_{a ∈ l} α a + ∑ j, β j · [arcA j ∈ l] · [arcB j ∈ l]`   (the quadratic cost).

Main results (`F` is the identity matrix, `C θ = adapterCost … θ …`, "face" means the doubly
stochastic matrices `X` with `X t s = 1`):

* `face_attains` : for every path `l` and every real `θ` there is a point `X` of the face with
  `C θ · (X − F) = δ + pathCost θ l`;
* `face_lower`   : for `θ` in the box, every point `X` of the face satisfies
  `C θ · (X − F) ≥ δ + pathCost θ l` for some path `l`;
* `adapter_forced_value` : hence, for `θ` in the box, the least value of `C θ · (X − F)` over the
  face exists and equals `δ +` the least path cost;
* `adapter_eta` : the least value of `C θ · (X − F)` over the face and over all scenarios of
  the box exists and equals `δ +` the least quadratic cost of a path.
-/

namespace DagCycleAssignment
namespace Adapter

open Finset Subdivision

variable {V A J : Type*}

section Costs

variable [DecidableEq A]

/-- Indicator that the arc `a` lies on the path `l`. -/
def ind (l : List A) (a : A) : ℝ := if a ∈ l then 1 else 0

theorem ind_binary (l : List A) (a : A) : ind l a = 0 ∨ ind l a = 1 := by
  unfold ind
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem ind_congr {l l' : List A} (h : ∀ a, a ∈ l ↔ a ∈ l') (a : A) : ind l a = ind l' a := by
  unfold ind
  by_cases ha : a ∈ l
  · rw [if_pos ha, if_pos ((h a).1 ha)]
  · rw [if_neg ha, if_neg (fun h' => ha ((h a).2 h'))]

variable [Fintype A] [Fintype J]

/-- The cost of the path `l` in the scenario `θ`. -/
def pathCost (arcA arcB : J → A) (α : A → ℝ) (β θ : J → ℝ) (l : List A) : ℝ :=
  ∑ a, α a * ind l a + ∑ j, (θ j * ind l (arcA j) + (β j - θ j) * ind l (arcB j))

/-- The quadratic cost of the path `l`. -/
def quadCost (arcA arcB : J → A) (α : A → ℝ) (β : J → ℝ) (l : List A) : ℝ :=
  ∑ a, α a * ind l a + ∑ j, β j * ind l (arcA j) * ind l (arcB j)

variable (arcA arcB : J → A) (α : A → ℝ) (β : J → ℝ)

theorem pathCost_congr (θ : J → ℝ) {l l' : List A} (h : ∀ a, a ∈ l ↔ a ∈ l') :
    pathCost arcA arcB α β θ l = pathCost arcA arcB α β θ l' := by
  unfold pathCost
  simp only [ind_congr h]

theorem quadCost_congr {l l' : List A} (h : ∀ a, a ∈ l ↔ a ∈ l') :
    quadCost arcA arcB α β l = quadCost arcA arcB α β l' := by
  unfold quadCost
  simp only [ind_congr h]

theorem quadCost_le_pathCost {θ : J → ℝ} (hθ : InBox β θ) (l : List A) :
    quadCost arcA arcB α β l ≤ pathCost arcA arcB α β θ l := by
  unfold quadCost pathCost
  have h : ∑ j, β j * ind l (arcA j) * ind l (arcB j)
      ≤ ∑ j, (θ j * ind l (arcA j) + (β j - θ j) * ind l (arcB j)) :=
    Finset.sum_le_sum fun j _ =>
      pair_lower (ind_binary l (arcA j)) (ind_binary l (arcB j)) (hθ j).1 (hθ j).2
  linarith

theorem pathCost_le_sum (hα : ∀ a, 0 ≤ α a) {θ : J → ℝ} (hθ : InBox β θ) (l : List A) :
    pathCost arcA arcB α β θ l ≤ ∑ a, α a + ∑ j, β j := by
  unfold pathCost
  have h1 : ∑ a, α a * ind l a ≤ ∑ a, α a := Finset.sum_le_sum fun a _ => by
    rcases ind_binary l a with h | h <;> rw [h] <;> simp [hα a]
  have h2 : ∑ j, (θ j * ind l (arcA j) + (β j - θ j) * ind l (arcB j)) ≤ ∑ j, β j :=
    Finset.sum_le_sum fun j _ =>
      (pair_bounds (ind_binary l (arcA j)) (ind_binary l (arcB j)) (hθ j).1 (hθ j).2).2
  linarith

/-- A scenario of the box in which the path `l` costs exactly its quadratic cost. -/
def pathScenario (l : List A) (j : J) : ℝ := if arcA j ∈ l then 0 else β j

omit [Fintype A] [Fintype J] in
theorem pathScenario_inBox (hβ : ∀ j, 0 ≤ β j) (l : List A) :
    InBox β (pathScenario arcA β l) := by
  intro j
  unfold pathScenario
  split_ifs
  · exact ⟨le_refl 0, hβ j⟩
  · exact ⟨hβ j, le_refl _⟩

theorem pathCost_pathScenario (l : List A) :
    pathCost arcA arcB α β (pathScenario arcA β l) l = quadCost arcA arcB α β l := by
  unfold pathCost quadCost
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : arcA j ∈ l
  · have h1 : ind l (arcA j) = 1 := by unfold ind; rw [if_pos h]
    have h2 : pathScenario arcA β l j = 0 := by unfold pathScenario; rw [if_pos h]
    rw [h1, h2]
    ring
  · have h1 : ind l (arcA j) = 0 := by unfold ind; rw [if_neg h]
    have h2 : pathScenario arcA β l j = β j := by unfold pathScenario; rw [if_neg h]
    rw [h1, h2]
    ring

end Costs

/-- A finite nonempty set of reals has a least element, and it is also the least element of
any larger set that it dominates from below. -/
theorem exists_isLeast_both {S T : Set ℝ} (hfin : S.Finite) (hne : S.Nonempty) (hsub : S ⊆ T)
    (hdom : ∀ x ∈ T, ∃ p ∈ S, p ≤ x) : ∃ m, IsLeast S m ∧ IsLeast T m := by
  obtain ⟨m, hm, hmin⟩ := Set.exists_min_image S id hfin hne
  refine ⟨m, ⟨hm, fun x hx => hmin x hx⟩, hsub hm, fun x hx => ?_⟩
  obtain ⟨p, hp, hpx⟩ := hdom x hx
  exact (hmin p hp).trans hpx

/-- The values of a function of paths that depends only on the set of arcs form a finite set. -/
theorem pathValues_finite [DecidableEq A] [Fintype A] (P : List A → Prop) (f : List A → ℝ)
    (hf : ∀ l l', (∀ a, a ∈ l ↔ a ∈ l') → f l = f l') :
    {x : ℝ | ∃ l, P l ∧ x = f l}.Finite := by
  refine (Set.finite_range
    (fun u : A → Bool => f (univ.filter (fun a => u a = true)).toList)).subset ?_
  rintro x ⟨l, _, rfl⟩
  refine ⟨fun a => decide (a ∈ l), ?_⟩
  apply hf
  intro a
  simp

variable [DecidableEq A] [Fintype J] [Fintype A] [Fintype V] [DecidableEq V]

section Value

variable (tail head : A → V) (arcA arcB : J → A) {s t : V} {α : A → ℝ} {β : J → ℝ} {δ H : ℝ}

omit [Fintype V] [Fintype A] in
theorem y_eq_ind {σ : Equiv.Perm (Vertex V A (chainLength arcA arcB))} {l : List A}
    (h : ∀ a, Used tail (chainLength arcA arcB) σ a ↔ a ∈ l) (a : A) :
    y tail arcA arcB σ a = ind l a := by
  unfold y ind
  by_cases ha : a ∈ l
  · rw [if_pos ((h a).2 ha), if_pos ha]
  · rw [if_neg (fun hu => ha ((h a).1 hu)), if_neg ha]

/-- The relative cost of a route whose used arcs are the arcs of the path `l`. -/
theorem relcost_eq_pathCost (θ : J → ℝ) (hst : s ≠ t)
    {σ : Equiv.Perm (Vertex V A (chainLength arcA arcB))}
    (hσ : Designated (Edge tail head (chainLength arcA arcB)) (Sum.inl s) (Sum.inl t) σ)
    (hret : σ (Sum.inl t) = Sum.inl s) {l : List A}
    (hl : ∀ a, Used tail (chainLength arcA arcB) σ a ↔ a ∈ l) :
    permCost (adapterCost tail head arcA arcB s t α β θ δ H) σ
        - permCost (adapterCost tail head arcA arcB s t α β θ δ H) (Equiv.refl _)
      = δ + pathCost arcA arcB α β θ l := by
  rw [adapter_cost_designated tail head arcA arcB s t α β θ δ H hst hσ, if_pos hret]
  simp only [y_eq_ind tail arcA arcB hl]
  unfold pathCost
  ring

/-- **Every path value is attained on the face**, for every real scenario. -/
theorem face_attains (θ : J → ℝ) (hst : s ≠ t) {N : ℕ} (rank : V → Fin N)
    (hA : ∀ a, rank (tail a) < rank (head a)) {l : List A} (W : IsWalk tail head s t l) :
    ∃ X : Matrix (Vertex V A (chainLength arcA arcB)) (Vertex V A (chainLength arcA arcB)) ℝ,
      X ∈ doublyStochastic ℝ (Vertex V A (chainLength arcA arcB)) ∧
      X (Sum.inl t) (Sum.inl s) = 1 ∧
      dot (adapterCost tail head arcA arcB s t α β θ δ H) X
          - permCost (adapterCost tail head arcA arcB s t α β θ δ H) (Equiv.refl _)
        = δ + pathCost arcA arcB α β θ l := by
  obtain ⟨σ, hσ, hret, hl⟩ :=
    exists_designated_of_walk tail head (chainLength arcA arcB) s t l rank hA hst W
  refine ⟨Equiv.Perm.permMatrix ℝ σ, permMatrix_mem_doublyStochastic, ?_, ?_⟩
  · rw [permMatrix_entry, if_pos hret]
  · rw [dot_permMatrix]
    exact relcost_eq_pathCost tail head arcA arcB θ hst hσ hret hl

/-- **Every point of the face is at least a path value**, for every scenario of the box. -/
theorem face_lower (hyp : Hyp s t α β δ H) {θ : J → ℝ} (hθ : InBox β θ) {N : ℕ}
    (rank : V → Fin N) (hA : ∀ a, rank (tail a) < rank (head a))
    (hpath : ∃ l, IsWalk tail head s t l)
    {X : Matrix (Vertex V A (chainLength arcA arcB)) (Vertex V A (chainLength arcA arcB)) ℝ}
    (hX : X ∈ doublyStochastic ℝ (Vertex V A (chainLength arcA arcB)))
    (hface : X (Sum.inl t) (Sum.inl s) = 1) :
    ∃ l, IsWalk tail head s t l ∧
      δ + pathCost arcA arcB α β θ l
        ≤ dot (adapterCost tail head arcA arcB s t α β θ δ H) X
          - permCost (adapterCost tail head arcA arcB s t α β θ δ H) (Equiv.refl _) := by
  obtain ⟨σ, hret, hle⟩ :=
    exists_perm_le_of_entry_one (adapterCost tail head arcA arcB s t α β θ δ H) hX hface
  have hle' : permCost (adapterCost tail head arcA arcB s t α β θ δ H) σ
      ≤ dot (adapterCost tail head arcA arcB s t α β θ δ H) X := hle
  by_cases hσ : Designated (Edge tail head (chainLength arcA arcB)) (Sum.inl s) (Sum.inl t) σ
  · obtain ⟨l, hl, hlU⟩ :=
      walk_of_designated tail head (chainLength arcA arcB) rank hA hyp.hst hσ hret
    refine ⟨l, hl, ?_⟩
    have h := relcost_eq_pathCost tail head arcA arcB (α := α) (β := β) (δ := δ) (H := H) θ
      hyp.hst hσ hret (fun a => (hlU a).symm)
    linarith
  · obtain ⟨l0, hl0⟩ := hpath
    refine ⟨l0, hl0, ?_⟩
    have h1 := completion_cost tail head arcA arcB hyp hθ hσ
    have h2 := pathCost_le_sum arcA arcB α β hyp.α_nonneg hθ l0
    linarith

/-- **The forced value in a scenario of the box.**  The least value of `C θ · (X − F)` over the
doubly stochastic matrices `X` with `X t s = 1` exists and equals `δ +` the least cost
`pathCost θ l` of a path `l` from `s` to `t` in the original graph. -/
theorem adapter_forced_value (hyp : Hyp s t α β δ H) {θ : J → ℝ} (hθ : InBox β θ) {N : ℕ}
    (rank : V → Fin N) (hA : ∀ a, rank (tail a) < rank (head a))
    (hpath : ∃ l, IsWalk tail head s t l) :
    ∃ m, IsLeast {x : ℝ | ∃ l, IsWalk tail head s t l ∧ x = δ + pathCost arcA arcB α β θ l} m ∧
      IsLeast {x : ℝ | ∃ X : Matrix (Vertex V A (chainLength arcA arcB))
          (Vertex V A (chainLength arcA arcB)) ℝ,
        X ∈ doublyStochastic ℝ (Vertex V A (chainLength arcA arcB)) ∧
        X (Sum.inl t) (Sum.inl s) = 1 ∧
        x = dot (adapterCost tail head arcA arcB s t α β θ δ H) X
          - permCost (adapterCost tail head arcA arcB s t α β θ δ H) (Equiv.refl _)} m := by
  refine exists_isLeast_both ?_ ?_ ?_ ?_
  · exact pathValues_finite (IsWalk tail head s t) (fun l => δ + pathCost arcA arcB α β θ l)
      (fun l l' h => congrArg (fun x => δ + x) (pathCost_congr arcA arcB α β θ h))
  · obtain ⟨l, hl⟩ := hpath
    exact ⟨_, l, hl, rfl⟩
  · rintro x ⟨l, hl, rfl⟩
    obtain ⟨X, hX, hface, hval⟩ :=
      face_attains tail head arcA arcB (α := α) (β := β) (δ := δ) (H := H) θ hyp.hst rank hA hl
    exact ⟨X, hX, hface, hval.symm⟩
  · rintro x ⟨X, hX, hface, rfl⟩
    obtain ⟨l, hl, hle⟩ := face_lower tail head arcA arcB hyp hθ rank hA hpath hX hface
    exact ⟨_, ⟨l, hl, rfl⟩, hle⟩

/-- **The value `η`.**  The least value of `C θ · (X − F)` over all scenarios `θ` of the box and
all doubly stochastic `X` with `X t s = 1` exists and equals `δ +` the least quadratic cost of a
path from `s` to `t` in the original graph. -/
theorem adapter_eta (hyp : Hyp s t α β δ H) {N : ℕ}
    (rank : V → Fin N) (hA : ∀ a, rank (tail a) < rank (head a))
    (hpath : ∃ l, IsWalk tail head s t l) :
    ∃ m, IsLeast {x : ℝ | ∃ l, IsWalk tail head s t l ∧ x = δ + quadCost arcA arcB α β l} m ∧
      IsLeast {x : ℝ | ∃ θ : J → ℝ, InBox β θ ∧
        ∃ X : Matrix (Vertex V A (chainLength arcA arcB))
          (Vertex V A (chainLength arcA arcB)) ℝ,
        X ∈ doublyStochastic ℝ (Vertex V A (chainLength arcA arcB)) ∧
        X (Sum.inl t) (Sum.inl s) = 1 ∧
        x = dot (adapterCost tail head arcA arcB s t α β θ δ H) X
          - permCost (adapterCost tail head arcA arcB s t α β θ δ H) (Equiv.refl _)} m := by
  refine exists_isLeast_both ?_ ?_ ?_ ?_
  · exact pathValues_finite (IsWalk tail head s t) (fun l => δ + quadCost arcA arcB α β l)
      (fun l l' h => congrArg (fun x => δ + x) (quadCost_congr arcA arcB α β h))
  · obtain ⟨l, hl⟩ := hpath
    exact ⟨_, l, hl, rfl⟩
  · rintro x ⟨l, hl, rfl⟩
    obtain ⟨X, hX, hface, hval⟩ :=
      face_attains tail head arcA arcB (α := α) (β := β) (δ := δ) (H := H)
        (pathScenario arcA β l) hyp.hst rank hA hl
    refine ⟨pathScenario arcA β l, pathScenario_inBox arcA β hyp.β_nonneg l, X, hX, hface, ?_⟩
    rw [hval, pathCost_pathScenario]
  · rintro x ⟨θ, hθ, X, hX, hface, rfl⟩
    obtain ⟨l, hl, hle⟩ := face_lower tail head arcA arcB hyp hθ rank hA hpath hX hface
    refine ⟨_, ⟨l, hl, rfl⟩, ?_⟩
    have h := quadCost_le_pathCost arcA arcB α β hθ l
    linarith

end Value

end Adapter
end DagCycleAssignment
