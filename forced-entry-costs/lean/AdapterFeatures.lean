import AdapterCost
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The cost matrix of the adapter and the scenario cost identity

Input: a finite directed graph with arcs `A` (`tail head : A → V`), terminals `s t`, linear
costs `α : A → ℝ`, and a finite list of interactions `J`; the interaction `j` has a first arc
`arcA j`, a second arc `arcB j` and a weight `β j`.  A scenario is `θ : J → ℝ`.

Construction (as in the paper).  An *incidence* is a pair `(j, side)`: the
interaction `j` meets its first arc (`side = true`, the A-feature) or its second arc
(`side = false`, the B-feature).  The chain of the arc `a` has the vertex `p_a` (index `0`)
followed, for the `i`-th incidence of `a` in a fixed order, by two fresh vertices (indices
`2i + 1` and `2i + 2`).  Costs:

* entry edge `tail a → p_a`: `α a`;
* step `2i` (connector into the feature): `0`;
* step `2i + 1` (the feature arc): `θ j` for an A-feature, `β j` for a B-feature;
* exit edge: `0`;  return entry `(t, s)`: `δ`;
* diagonal: `θ j` at the first vertex of a B-feature (index `2i + 1`), `0` elsewhere;
* every other off-diagonal entry: `H`.

So `θ j` occurs in exactly two entries: the feature arc of the A-feature of `j` and the
diagonal entry at the first vertex of the B-feature of `j`.

Main results, for every real scenario `θ` (no interval is needed for the identity):

* `card_vertex` : the instance has `|V| + |A| + 4 |J|` rows and columns;
* `adapterCost_feature_arc`, `adapterCost_feature_diag` : the two entries that carry `θ j`;
* `adapter_identity_cost` : the identity costs `∑ j, θ j`;
* `adapter_cost_designated`, `adapter_cost_path`, `adapter_cost_route` :
    cost(σ) − cost(identity) = δ + ∑ a, α a · y a + ∑ j, (θ j · y (arcA j) + (β j − θ j) · y (arcB j)),
  where `y a ∈ {0, 1}` says whether the arc `a` is used;
* `pair_lower`, `pair_attained` : `min over θ ∈ [0, β] of θ u + (β − θ) v = β u v` for binary `u, v`;
* `adapter_min_over_scenarios` : for a fixed route, the minimum over the box of scenarios is
    δ + ∑ a, α a · y a + ∑ j, β j · y (arcA j) · y (arcB j).
-/

namespace DagCycleAssignment
namespace Adapter

open Finset Subdivision

variable {V A J : Type*}

/-- An interaction together with the side on which it meets an arc
(`true`: its first arc, the A-feature; `false`: its second arc, the B-feature). -/
abbrev Incidence (J : Type*) := J × Bool

/-- The arc that carries an incidence. -/
def arcOf (arcA arcB : J → A) (p : Incidence J) : A := if p.2 then arcA p.1 else arcB p.1

/-- Cost of the feature arc: `θ j` for the A-feature, `β j` for the B-feature. -/
def featureArc (β θ : J → ℝ) (p : Incidence J) : ℝ := if p.2 then θ p.1 else β p.1

/-- Diagonal entry at the first vertex of a feature: `θ j` for the B-feature, `0` for the
A-feature. -/
def featureDiag (θ : J → ℝ) (p : Incidence J) : ℝ := if p.2 then 0 else θ p.1

/-! ### Sums over odd positions -/

theorem sum_range_odd (g : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ range (2 * m), (if k % 2 = 1 then g (k / 2) else 0) = ∑ i ∈ range m, g i := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h1 : (2 * m + 1) % 2 = 1 := by omega
      have h2 : (2 * m + 1) / 2 = m := by omega
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, ih, Finset.sum_range_succ, if_neg (by omega), if_pos h1, h2,
        add_zero]

theorem fin_sum_odd (g : ℕ → ℝ) (m : ℕ) :
    ∑ j : Fin (2 * m), (if j.val % 2 = 1 then g (j.val / 2) else 0) = ∑ i : Fin m, g i.val := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k % 2 = 1 then g (k / 2) else 0) (2 * m),
    sum_range_odd, ← Fin.sum_univ_eq_sum_range g m]

theorem fin_sum_odd_succ (g : ℕ → ℝ) (m : ℕ) :
    ∑ j : Fin (2 * m + 1), (if j.val % 2 = 1 then g (j.val / 2) else 0)
      = ∑ i : Fin m, g i.val := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k % 2 = 1 then g (k / 2) else 0) (2 * m + 1),
    Finset.sum_range_succ, sum_range_odd, if_neg (by omega), add_zero,
    ← Fin.sum_univ_eq_sum_range g m]

variable [DecidableEq A] [Fintype J]

/-- The incidences of the arc `a`. -/
abbrev Fiber (arcA arcB : J → A) (a : A) := {p : Incidence J // arcOf arcA arcB p = a}

/-- The number of incidences of `a`. -/
def mult (arcA arcB : J → A) (a : A) : ℕ := Fintype.card (Fiber arcA arcB a)

/-- The fixed order in which the incidences of `a` are processed. -/
noncomputable def slot (arcA arcB : J → A) (a : A) :
    Fin (mult arcA arcB a) ≃ Fiber arcA arcB a :=
  (Fintype.equivFin (Fiber arcA arcB a)).symm

/-- The chain of `a` has two steps for each incidence. -/
def chainLength (arcA arcB : J → A) (a : A) : ℕ := 2 * mult arcA arcB a

/-- The value of `f` at the `n`-th incidence of `a` (`0` if there is none). -/
noncomputable def atSlot (arcA arcB : J → A) (f : Incidence J → ℝ) (a : A) (n : ℕ) : ℝ :=
  if h : n < mult arcA arcB a then f (slot arcA arcB a ⟨n, h⟩).1 else 0

/-- Step costs of the chain of `a`: step `2i` is a connector, step `2i + 1` is the feature arc
of the `i`-th incidence. -/
noncomputable def stepCost (arcA arcB : J → A) (β θ : J → ℝ) (a : A) (n : ℕ) : ℝ :=
  if n % 2 = 1 then atSlot arcA arcB (featureArc β θ) a (n / 2) else 0

/-- Diagonal costs of the chain of `a`: internal vertex `2i + 1` is the first vertex of the
feature of the `i`-th incidence. -/
noncomputable def diagCost (arcA arcB : J → A) (θ : J → ℝ) (a : A) (n : ℕ) : ℝ :=
  if n % 2 = 1 then atSlot arcA arcB (featureDiag θ) a (n / 2) else 0

theorem sum_atSlot (arcA arcB : J → A) (f : Incidence J → ℝ) (a : A) :
    ∑ i : Fin (mult arcA arcB a), atSlot arcA arcB f a i.val
      = ∑ p : Fiber arcA arcB a, f p.1 := by
  rw [← Equiv.sum_comp (slot arcA arcB a) (fun p => f p.1)]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold atSlot
  rw [dif_pos i.isLt]

/-- The step costs of a chain add up to the feature-arc costs of its incidences. -/
theorem sum_stepCost (arcA arcB : J → A) (β θ : J → ℝ) (a : A) :
    ∑ j : Fin (chainLength arcA arcB a), stepCost arcA arcB β θ a j.val
      = ∑ p : Fiber arcA arcB a, featureArc β θ p.1 := by
  rw [← sum_atSlot]
  exact fin_sum_odd (atSlot arcA arcB (featureArc β θ) a) (mult arcA arcB a)

/-- The diagonal costs of a chain add up to the diagonal costs of its incidences. -/
theorem sum_diagCost (arcA arcB : J → A) (θ : J → ℝ) (a : A) :
    ∑ i : Fin (chainLength arcA arcB a + 1), diagCost arcA arcB θ a i.val
      = ∑ p : Fiber arcA arcB a, featureDiag θ p.1 := by
  rw [← sum_atSlot]
  exact fin_sum_odd_succ (atSlot arcA arcB (featureDiag θ) a) (mult arcA arcB a)

theorem sum_fiber (arcA arcB : J → A) (f : Incidence J → ℝ) (a : A) :
    ∑ p : Fiber arcA arcB a, f p.1
      = ∑ p : Incidence J, (if arcOf arcA arcB p = a then f p else 0) := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (univ.filter fun p => arcOf arcA arcB p = a) (by simp) f).symm

variable [Fintype A]

/-- Regrouping: a sum over arcs of sums over their incidences is a sum over interactions. -/
theorem sum_arcs_incidences (arcA arcB : J → A) (w : A → ℝ) (f : Incidence J → ℝ) :
    ∑ a, w a * ∑ p : Fiber arcA arcB a, f p.1
      = ∑ j, (w (arcA j) * f (j, true) + w (arcB j) * f (j, false)) := by
  have h : ∀ p : Incidence J,
      ∑ a, w a * (if arcOf arcA arcB p = a then f p else 0) = w (arcOf arcA arcB p) * f p := by
    intro p
    simp [mul_ite, Finset.sum_ite_eq]
  simp only [sum_fiber, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_congr rfl (fun p _ => h p), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp [arcOf]

/-- The number of incidences is twice the number of interactions. -/
theorem sum_mult (arcA arcB : J → A) : ∑ a, mult arcA arcB a = 2 * Fintype.card J := by
  have h : ∑ a, mult arcA arcB a = Fintype.card (Incidence J) := by
    unfold mult
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv (arcOf arcA arcB))
  rw [h, Fintype.card_prod, Fintype.card_bool, mul_comm]

variable [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- **The dimension of the assignment instance**: `N = |V| + |A| + 4 |J|`. -/
theorem card_vertex (arcA arcB : J → A) :
    Fintype.card (Vertex V A (chainLength arcA arcB))
      = Fintype.card V + Fintype.card A + 4 * Fintype.card J := by
  have h : ∑ a : A, (chainLength arcA arcB a + 1) = 2 * ∑ a, mult arcA arcB a + Fintype.card A := by
    unfold chainLength
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  rw [Fintype.card_sum, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [h, sum_mult]
  omega

section Matrix

variable (tail head : A → V) (arcA arcB : J → A) (s t : V) (α : A → ℝ) (β θ : J → ℝ) (δ H : ℝ)

/-- **The cost matrix of the adapter** in the scenario `θ`. -/
noncomputable def adapterCost :
    Vertex V A (chainLength arcA arcB) → Vertex V A (chainLength arcA arcB) → ℝ :=
  cost tail head (chainLength arcA arcB) s t α (stepCost arcA arcB β θ) (diagCost arcA arcB θ) δ H

/-- Indicator that the arc `a` is used by `σ`. -/
def y (σ : Equiv.Perm (Vertex V A (chainLength arcA arcB))) (a : A) : ℝ :=
  if Used tail (chainLength arcA arcB) σ a then 1 else 0

omit [Fintype A] [Fintype V] in
theorem y_binary (σ : Equiv.Perm (Vertex V A (chainLength arcA arcB))) (a : A) :
    y tail arcA arcB σ a = 0 ∨ y tail arcA arcB σ a = 1 := by
  unfold y
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

omit [Fintype A] [Fintype V] in
/-- The feature arc of the `i`-th incidence of `a` joins the internal vertices `2i + 1` and
`2i + 2` of its chain and costs `θ j` for an A-feature and `β j` for a B-feature. -/
theorem adapterCost_feature_arc (a : A) (i : Fin (mult arcA arcB a)) :
    adapterCost tail head arcA arcB s t α β θ δ H
        (internal (chainLength arcA arcB) a
          (⟨2 * i.val + 1, by have := i.isLt; unfold chainLength; omega⟩ :
            Fin (chainLength arcA arcB a)).castSucc)
        (internal (chainLength arcA arcB) a
          (⟨2 * i.val + 1, by have := i.isLt; unfold chainLength; omega⟩ :
            Fin (chainLength arcA arcB a)).succ)
      = featureArc β θ (slot arcA arcB a i).1 := by
  unfold adapterCost
  rw [cost_step]
  have h1 : (2 * i.val + 1) % 2 = 1 := by omega
  have h2 : (2 * i.val + 1) / 2 = i.val := by omega
  simp only [stepCost, atSlot, h1, h2, if_true, dif_pos i.isLt]

omit [Fintype A] [Fintype V] in
/-- The diagonal entry at the first vertex of the feature of the `i`-th incidence of `a`
(internal vertex `2i + 1`) is `θ j` for a B-feature and `0` for an A-feature. -/
theorem adapterCost_feature_diag (a : A) (i : Fin (mult arcA arcB a)) :
    adapterCost tail head arcA arcB s t α β θ δ H
        (internal (chainLength arcA arcB) a
          (⟨2 * i.val + 1, by have := i.isLt; unfold chainLength; omega⟩ :
            Fin (chainLength arcA arcB a + 1)))
        (internal (chainLength arcA arcB) a
          (⟨2 * i.val + 1, by have := i.isLt; unfold chainLength; omega⟩ :
            Fin (chainLength arcA arcB a + 1)))
      = featureDiag θ (slot arcA arcB a i).1 := by
  unfold adapterCost
  rw [cost_internal_self]
  have h1 : (2 * i.val + 1) % 2 = 1 := by omega
  have h2 : (2 * i.val + 1) / 2 = i.val := by omega
  simp only [diagCost, atSlot, h1, h2, if_true, dif_pos i.isLt]

/-- A scenario that minimises the cost of the route `σ`: `θ j = 0` if the first arc of `j` is
used, `θ j = β j` otherwise. -/
def minScenario (σ : Equiv.Perm (Vertex V A (chainLength arcA arcB))) (j : J) : ℝ :=
  if Used tail (chainLength arcA arcB) σ (arcA j) then 0 else β j

/-- The identity costs `∑ j, θ j`. -/
theorem adapter_identity_cost :
    permCost (adapterCost tail head arcA arcB s t α β θ δ H) (Equiv.refl _) = ∑ j, θ j := by
  unfold adapterCost
  rw [permCost_refl, Finset.sum_congr rfl (fun a _ => sum_diagCost arcA arcB θ a)]
  have h := sum_arcs_incidences arcA arcB (fun _ => (1 : ℝ)) (featureDiag θ)
  simp only [one_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [featureDiag]

/-- **Scenario cost identity for a designated permutation.**  Derived from the cost matrix
`adapterCost`; nothing about costs is assumed. -/
theorem adapter_cost_designated (hst : s ≠ t)
    {σ : Equiv.Perm (Vertex V A (chainLength arcA arcB))}
    (hσ : Designated (Edge tail head (chainLength arcA arcB)) (Sum.inl s) (Sum.inl t) σ) :
    permCost (adapterCost tail head arcA arcB s t α β θ δ H) σ
        - permCost (adapterCost tail head arcA arcB s t α β θ δ H) (Equiv.refl _) =
      (if σ (Sum.inl t) = Sum.inl s then δ else 0)
        + ∑ a, α a * y tail arcA arcB σ a
        + ∑ j, (θ j * y tail arcA arcB σ (arcA j) + (β j - θ j) * y tail arcA arcB σ (arcB j)) := by
  unfold adapterCost
  rw [permCost_designated tail head (chainLength arcA arcB) s t α (stepCost arcA arcB β θ)
    (diagCost arcA arcB θ) δ H hst hσ]
  have harc : ∀ a, (if Used tail (chainLength arcA arcB) σ a then
        α a + ∑ j : Fin (chainLength arcA arcB a), stepCost arcA arcB β θ a j.val
          - ∑ i : Fin (chainLength arcA arcB a + 1), diagCost arcA arcB θ a i.val
      else 0)
      = α a * y tail arcA arcB σ a
        + y tail arcA arcB σ a
          * ∑ p : Fiber arcA arcB a, (featureArc β θ p.1 - featureDiag θ p.1) := by
    intro a
    rw [sum_stepCost, sum_diagCost, Finset.sum_sub_distrib]
    unfold y
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun a _ => harc a), Finset.sum_add_distrib,
    sum_arcs_incidences arcA arcB (y tail arcA arcB σ)
      (fun p => featureArc β θ p - featureDiag θ p), add_assoc]
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [featureArc, featureDiag, if_true, if_false, Bool.false_eq_true]
  ring

/-- **Scenario cost identity for the permutation of a path.**  For every simple directed path
`P` from `s` to `t` in the subdivided graph. -/
theorem adapter_cost_path (hst : s ≠ t)
    (P : SimplePath (Edge tail head (chainLength arcA arcB)) (Sum.inl s) (Sum.inl t)) :
    permCost (adapterCost tail head arcA arcB s t α β θ δ H) P.toPerm
        - permCost (adapterCost tail head arcA arcB s t α β θ δ H) (Equiv.refl _) =
      δ + ∑ a, α a * y tail arcA arcB P.toPerm a
        + ∑ j, (θ j * y tail arcA arcB P.toPerm (arcA j)
            + (β j - θ j) * y tail arcA arcB P.toPerm (arcB j)) := by
  rw [adapter_cost_designated tail head arcA arcB s t α β θ δ H hst P.toPerm_designated,
    if_pos P.toPerm_return]

/-- **Scenario cost identity for a non-identity designated permutation**, when the original
graph is acyclic (certified by a rank increasing along every arc). -/
theorem adapter_cost_route {N : ℕ} (rank : V → Fin N)
    (hA : ∀ a, rank (tail a) < rank (head a)) (hst : s ≠ t)
    {σ : Equiv.Perm (Vertex V A (chainLength arcA arcB))}
    (hσ : Designated (Edge tail head (chainLength arcA arcB)) (Sum.inl s) (Sum.inl t) σ)
    (hne : σ ≠ Equiv.refl _) :
    permCost (adapterCost tail head arcA arcB s t α β θ δ H) σ
        - permCost (adapterCost tail head arcA arcB s t α β θ δ H) (Equiv.refl _) =
      δ + ∑ a, α a * y tail arcA arcB σ a
        + ∑ j, (θ j * y tail arcA arcB σ (arcA j) + (β j - θ j) * y tail arcA arcB σ (arcB j)) := by
  have hL : ∀ a, chainLength arcA arcB a + 1 ≤ 2 * Fintype.card (Incidence J) + 1 := by
    intro a
    have h : Fintype.card (Fiber arcA arcB a) ≤ Fintype.card (Incidence J) :=
      Fintype.card_subtype_le _
    unfold chainLength mult
    omega
  have hret : σ (Sum.inl t) = Sum.inl s :=
    return_used (liftedRank rank tail (chainLength arcA arcB) hL)
      (fun {_ _} h => edge_increases_rank rank tail head (chainLength arcA arcB) hL hA h) hσ hne
  rw [adapter_cost_designated tail head arcA arcB s t α β θ δ H hst hσ, if_pos hret]

end Matrix

/-! ### The minimum over scenarios -/

omit [DecidableEq A] [Fintype J] [Fintype A] [Fintype V] [DecidableEq V] in
theorem pair_lower {β θ u v : ℝ} (hu : u = 0 ∨ u = 1) (hv : v = 0 ∨ v = 1)
    (h0 : 0 ≤ θ) (h1 : θ ≤ β) : β * u * v ≤ θ * u + (β - θ) * v := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp <;> linarith

omit [DecidableEq A] [Fintype J] [Fintype A] [Fintype V] [DecidableEq V] in
theorem pair_attained {β u : ℝ} (v : ℝ) (hβ : 0 ≤ β) (hu : u = 0 ∨ u = 1) :
    ∃ θ, 0 ≤ θ ∧ θ ≤ β ∧ θ * u + (β - θ) * v = β * u * v := by
  rcases hu with rfl | rfl
  · exact ⟨β, hβ, le_refl β, by ring⟩
  · exact ⟨0, le_refl 0, hβ, by ring⟩

/-- **The minimum over the box of scenarios, for a fixed route.**  The value
`δ + ∑ a, α a · y a + ∑ j, β j · y (arcA j) · y (arcB j)` is a lower bound for every scenario
`0 ≤ θ ≤ β` and is attained by an explicit scenario. -/
theorem adapter_min_over_scenarios (tail head : A → V) (arcA arcB : J → A) (s t : V)
    (α : A → ℝ) (β : J → ℝ) (δ H : ℝ) (hβ : ∀ j, 0 ≤ β j) (hst : s ≠ t)
    (P : SimplePath (Edge tail head (chainLength arcA arcB)) (Sum.inl s) (Sum.inl t)) :
    (∀ θ : J → ℝ, (∀ j, 0 ≤ θ j ∧ θ j ≤ β j) →
        δ + ∑ a, α a * y tail arcA arcB P.toPerm a
            + ∑ j, β j * y tail arcA arcB P.toPerm (arcA j) * y tail arcA arcB P.toPerm (arcB j)
          ≤ permCost (adapterCost tail head arcA arcB s t α β θ δ H) P.toPerm
              - permCost (adapterCost tail head arcA arcB s t α β θ δ H) (Equiv.refl _)) ∧
    (∃ θ : J → ℝ, (∀ j, 0 ≤ θ j ∧ θ j ≤ β j) ∧
        permCost (adapterCost tail head arcA arcB s t α β θ δ H) P.toPerm
            - permCost (adapterCost tail head arcA arcB s t α β θ δ H) (Equiv.refl _)
          = δ + ∑ a, α a * y tail arcA arcB P.toPerm a
            + ∑ j, β j * y tail arcA arcB P.toPerm (arcA j)
                * y tail arcA arcB P.toPerm (arcB j)) := by
  constructor
  · intro θ hθ
    rw [adapter_cost_path tail head arcA arcB s t α β θ δ H hst P]
    have h : ∑ j, β j * y tail arcA arcB P.toPerm (arcA j) * y tail arcA arcB P.toPerm (arcB j)
        ≤ ∑ j, (θ j * y tail arcA arcB P.toPerm (arcA j)
            + (β j - θ j) * y tail arcA arcB P.toPerm (arcB j)) :=
      Finset.sum_le_sum fun j _ =>
        pair_lower (y_binary tail arcA arcB P.toPerm (arcA j))
          (y_binary tail arcA arcB P.toPerm (arcB j)) (hθ j).1 (hθ j).2
    linarith
  · refine ⟨minScenario tail arcA arcB β P.toPerm, ?_, ?_⟩
    · intro j
      unfold minScenario
      split_ifs
      · exact ⟨le_refl 0, hβ j⟩
      · exact ⟨hβ j, le_refl _⟩
    · rw [adapter_cost_path tail head arcA arcB s t α β _ δ H hst P]
      have hpt : ∀ j, minScenario tail arcA arcB β P.toPerm j * y tail arcA arcB P.toPerm (arcA j)
            + (β j - minScenario tail arcA arcB β P.toPerm j) * y tail arcA arcB P.toPerm (arcB j)
          = β j * y tail arcA arcB P.toPerm (arcA j) * y tail arcA arcB P.toPerm (arcB j) := by
        intro j
        by_cases hu : Used tail (chainLength arcA arcB) P.toPerm (arcA j)
        · have h1 : y tail arcA arcB P.toPerm (arcA j) = 1 := by unfold y; rw [if_pos hu]
          have h2 : minScenario tail arcA arcB β P.toPerm j = 0 := by
            unfold minScenario; rw [if_pos hu]
          rw [h1, h2]
          ring
        · have h1 : y tail arcA arcB P.toPerm (arcA j) = 0 := by unfold y; rw [if_neg hu]
          have h2 : minScenario tail arcA arcB β P.toPerm j = β j := by
            unfold minScenario; rw [if_neg hu]
          rw [h1, h2]
          ring
      rw [Finset.sum_congr rfl (fun j _ => hpt j)]

end Adapter
end DagCycleAssignment
