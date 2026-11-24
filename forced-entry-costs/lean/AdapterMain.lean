import AdapterTheorem
import AdapterPattern

/-!
# The exact adapter theorem: summary statement

`exact_adapter` collects, for one instance, everything proved in the other modules.

Input: finite types `V` (vertices), `A` (arcs), `J` (interactions); `tail head : A → V`;
`arcA arcB : J → A` (the two arcs of an interaction); terminals `s t`; arc costs `α`;
interaction weights `β`; the cost `δ` of the return entry; the completion cost `H`.

Hypotheses: `Hyp` (`s ≠ t`, `α ≥ 0`, `β ≥ 0`, `δ > 0`, `H ≥ δ + ∑ α + 2 ∑ β + 1`); a rank that
increases along every arc (the graph is acyclic); at least one path from `s` to `t`.

The assignment instance has the vertex set `Vertex V A (chainLength arcA arcB)` as its rows and
columns and the cost matrix `adapterCost … θ …` in the scenario `θ`; the identity matrix is the
supplied assignment `F`, and the observed entry is `(t, s)`.
-/

namespace DagCycleAssignment
namespace Adapter

open Finset Subdivision

variable {V A J : Type*} [DecidableEq A] [Fintype J] [Fintype A] [Fintype V] [DecidableEq V]

/-- **The exact adapter theorem.** -/
theorem exact_adapter (tail head : A → V) (arcA arcB : J → A) {s t : V} {α : A → ℝ}
    {β : J → ℝ} {δ H : ℝ} (hyp : Hyp s t α β δ H) {N : ℕ} (rank : V → Fin N)
    (hA : ∀ a, rank (tail a) < rank (head a)) (hpath : ∃ l, IsWalk tail head s t l) :
    -- the dimension
    (Fintype.card (Vertex V A (chainLength arcA arcB))
      = Fintype.card V + Fintype.card A + 4 * Fintype.card J) ∧
    -- (C2): each parameter occurs in exactly the entries of its two incidences, with
    -- coefficient 1; the entry of an incidence is diagonal exactly for the B-feature
    (∀ (θ : J → ℝ) (x y : Vertex V A (chainLength arcA arcB)),
      adapterCost tail head arcA arcB s t α β θ δ H x y
        = adapterCost tail head arcA arcB s t α β (fun _ => 0) δ H x y
          + ∑ p : Incidence J,
              θ p.1 * (if x = uRow V arcA arcB p ∧ y = uCol V arcA arcB p then 1 else 0)) ∧
    (∀ p : Incidence J, uRow V arcA arcB p = uCol V arcA arcB p ↔ p.2 = false) ∧
    -- (C3): the uncertain entries have pairwise different rows and pairwise different columns
    Function.Injective (uRow V arcA arcB) ∧ Function.Injective (uCol V arcA arcB) ∧
    -- for every scenario of the box
    (∀ θ : J → ℝ, InBox β θ →
      -- (C4): all entries are nonnegative
      (∀ x y, 0 ≤ adapterCost tail head arcA arcB s t α β θ δ H x y) ∧
      -- (C1): the explicit dual certificate
      ((∀ x y, dualRow arcA arcB θ x + 0 ≤ adapterCost tail head arcA arcB s t α β θ δ H x y) ∧
        (∀ x, dualRow arcA arcB θ x + 0 = adapterCost tail head arcA arcB s t α β θ δ H x x) ∧
        (∑ x : Vertex V A (chainLength arcA arcB), dualRow arcA arcB θ x
            + ∑ _x : Vertex V A (chainLength arcA arcB), (0 : ℝ)
          = permCost (adapterCost tail head arcA arcB s t α β θ δ H) (Equiv.refl _))) ∧
      -- (C1): the identity is the unique optimum among all doubly stochastic matrices
      (∀ X : Matrix (Vertex V A (chainLength arcA arcB)) (Vertex V A (chainLength arcA arcB)) ℝ,
        X ∈ doublyStochastic ℝ (Vertex V A (chainLength arcA arcB)) → X ≠ 1 →
        permCost (adapterCost tail head arcA arcB s t α β θ δ H) (Equiv.refl _)
          < dot (adapterCost tail head arcA arcB s t α β θ δ H) X) ∧
      -- the forced value: least value on the face `X t s = 1` = δ + least path cost
      (∃ m, IsLeast {x : ℝ | ∃ l, IsWalk tail head s t l ∧
            x = δ + pathCost arcA arcB α β θ l} m ∧
        IsLeast {x : ℝ | ∃ X : Matrix (Vertex V A (chainLength arcA arcB))
            (Vertex V A (chainLength arcA arcB)) ℝ,
          X ∈ doublyStochastic ℝ (Vertex V A (chainLength arcA arcB)) ∧
          X (Sum.inl t) (Sum.inl s) = 1 ∧
          x = dot (adapterCost tail head arcA arcB s t α β θ δ H) X
            - permCost (adapterCost tail head arcA arcB s t α β θ δ H) (Equiv.refl _)} m)) ∧
    -- the value η: least forced value over the box = δ + least quadratic path cost
    (∃ m, IsLeast {x : ℝ | ∃ l, IsWalk tail head s t l ∧ x = δ + quadCost arcA arcB α β l} m ∧
      IsLeast {x : ℝ | ∃ θ : J → ℝ, InBox β θ ∧
        ∃ X : Matrix (Vertex V A (chainLength arcA arcB))
          (Vertex V A (chainLength arcA arcB)) ℝ,
        X ∈ doublyStochastic ℝ (Vertex V A (chainLength arcA arcB)) ∧
        X (Sum.inl t) (Sum.inl s) = 1 ∧
        x = dot (adapterCost tail head arcA arcB s t α β θ δ H) X
          - permCost (adapterCost tail head arcA arcB s t α β θ δ H) (Equiv.refl _)} m) :=
  ⟨card_vertex arcA arcB,
    fun θ x y => adapterCost_affine V arcA arcB tail head s t α β θ δ H x y,
    uRow_eq_uCol_iff V arcA arcB,
    uRow_injective V arcA arcB,
    uCol_injective V arcA arcB,
    fun _ hθ =>
      ⟨adapterCost_nonneg tail head arcA arcB hyp hθ,
        dual_certificate tail head arcA arcB hyp hθ,
        fun _ hX hne => identity_unique_optimal tail head arcA arcB hyp hθ rank hA hX hne,
        adapter_forced_value tail head arcA arcB hyp hθ rank hA hpath⟩,
    adapter_eta tail head arcA arcB hyp rank hA hpath⟩

end Adapter
end DagCycleAssignment
