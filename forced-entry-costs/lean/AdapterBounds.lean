import AdapterFeatures
import Mathlib.Data.Matrix.DoublyStochastic

/-!
# The adapter on the box of scenarios: nonnegativity, dual certificate, completion

Hypotheses (`Hyp`): `s ≠ t`, `α ≥ 0`, `β ≥ 0`, `δ > 0` and `H ≥ δ + ∑ α + 2 ∑ β + 1`.
A scenario `θ` is in the box (`InBox β θ`) if `0 ≤ θ j ≤ β j` for every `j`.

* `adapterCost_nonneg`   every entry is nonnegative on the box;
* `dual_certificate`     the row prices `dualRow` (the diagonal entries: `θ j` at the first
                         vertex of the B-feature of `j`, `0` elsewhere) and zero column prices are
                         dual feasible, tight on the diagonal, and their total is the cost of the
                         identity;
* `identity_optimal`     hence the identity is optimal among all doubly stochastic matrices;
* `completion_cost`      a permutation that uses a completion entry costs at least
                         `δ + ∑ α + ∑ β + 1` more than the identity;
* `designated_cost_bounds`  a non-identity designated permutation costs between `δ` and
                         `δ + ∑ α + ∑ β` more than the identity;
* `perm_cost_ge`         every non-identity permutation costs at least `δ` more than the identity.
-/

namespace DagCycleAssignment

open Finset

namespace Subdivision

variable {V A : Type*} [DecidableEq V] [DecidableEq A]

section Generic

variable (tail head : A → V) (length : A → ℕ) (s t : V) (α : A → ℝ)
  (stepCost diagCost : A → ℕ → ℝ) (δ H : ℝ)

theorem cost_nonneg (hα : ∀ a, 0 ≤ α a) (hstep : ∀ a n, 0 ≤ stepCost a n)
    (hdiag : ∀ a n, 0 ≤ diagCost a n) (hδ : 0 ≤ δ) (hH : 0 ≤ H) (x y : Vertex V A length) :
    0 ≤ cost tail head length s t α stepCost diagCost δ H x y := by
  rcases x with u | ⟨a, i⟩ <;> rcases y with v | ⟨b, k⟩
  · show 0 ≤ (if u = v then 0 else if u = t ∧ v = s then δ else H)
    split_ifs <;> first | exact le_refl _ | exact hδ | exact hH
  · show 0 ≤ (if u = tail b ∧ k.val = 0 then α b else H)
    split_ifs <;> first | exact hα _ | exact hH
  · show 0 ≤ (if i.val = length a ∧ v = head a then 0 else H)
    split_ifs <;> first | exact le_refl _ | exact hH
  · show 0 ≤ (if a = b then (if k.val = i.val then diagCost a i.val
        else if k.val = i.val + 1 then stepCost a i.val else H) else H)
    split_ifs <;> first | exact hdiag _ _ | exact hstep _ _ | exact hH

/-- The diagonal entry is the smallest entry of its row. -/
theorem cost_diag_le (hα : ∀ a, 0 ≤ α a) (hδ : 0 ≤ δ) (hH : 0 ≤ H)
    (h1 : ∀ a n, diagCost a n ≤ stepCost a n) (h2 : ∀ a n, diagCost a n ≤ H)
    (h3 : ∀ a, diagCost a (length a) ≤ 0) (x y : Vertex V A length) :
    cost tail head length s t α stepCost diagCost δ H x x
      ≤ cost tail head length s t α stepCost diagCost δ H x y := by
  rcases x with u | ⟨a, i⟩
  · have hd : cost tail head length s t α stepCost diagCost δ H (Sum.inl u) (Sum.inl u) = 0 :=
      cost_inl_self tail head length s t α stepCost diagCost δ H u
    rw [hd]
    rcases y with v | ⟨b, k⟩
    · show 0 ≤ (if u = v then 0 else if u = t ∧ v = s then δ else H)
      split_ifs <;> first | exact le_refl _ | exact hδ | exact hH
    · show 0 ≤ (if u = tail b ∧ k.val = 0 then α b else H)
      split_ifs <;> first | exact hα _ | exact hH
  · have hd : cost tail head length s t α stepCost diagCost δ H (Sum.inr ⟨a, i⟩) (Sum.inr ⟨a, i⟩)
        = diagCost a i.val :=
      cost_internal_self tail head length s t α stepCost diagCost δ H a i
    rw [hd]
    rcases y with v | ⟨b, k⟩
    · show diagCost a i.val ≤ (if i.val = length a ∧ v = head a then 0 else H)
      split_ifs with h
      · rw [h.1]
        exact h3 a
      · exact h2 _ _
    · show diagCost a i.val ≤ (if a = b then (if k.val = i.val then diagCost a i.val
          else if k.val = i.val + 1 then stepCost a i.val else H) else H)
      split_ifs <;> first | exact le_refl _ | exact h1 _ _ | exact h2 _ _

end Generic

end Subdivision

namespace Adapter

open Subdivision

variable {V A J : Type*}

/-- The box of scenarios. -/
def InBox (β θ : J → ℝ) : Prop := ∀ j, 0 ≤ θ j ∧ θ j ≤ β j

/-- The numerical hypotheses of the adapter theorem. -/
structure Hyp [Fintype A] [Fintype J] (s t : V) (α : A → ℝ) (β : J → ℝ) (δ H : ℝ) : Prop where
  hst : s ≠ t
  α_nonneg : ∀ a, 0 ≤ α a
  β_nonneg : ∀ j, 0 ≤ β j
  δ_pos : 0 < δ
  H_large : δ + ∑ a, α a + 2 * ∑ j, β j + 1 ≤ H

section Pointwise

variable {β θ : J → ℝ}

theorem featureArc_nonneg (hβ : ∀ j, 0 ≤ β j) (hθ : InBox β θ) (p : Incidence J) :
    0 ≤ featureArc β θ p := by
  unfold featureArc
  split_ifs
  · exact (hθ _).1
  · exact hβ _

theorem featureDiag_nonneg (hθ : InBox β θ) (p : Incidence J) : 0 ≤ featureDiag θ p := by
  unfold featureDiag
  split_ifs
  · exact le_refl 0
  · exact (hθ _).1

theorem featureDiag_le_arc (hθ : InBox β θ) (p : Incidence J) :
    featureDiag θ p ≤ featureArc β θ p := by
  unfold featureDiag featureArc
  split_ifs
  · exact (hθ _).1
  · exact (hθ _).2

theorem featureDiag_le_sum [Fintype J] (hβ : ∀ j, 0 ≤ β j) (hθ : InBox β θ) (p : Incidence J) :
    featureDiag θ p ≤ ∑ j, β j := by
  unfold featureDiag
  split_ifs
  · exact Finset.sum_nonneg fun j _ => hβ j
  · exact ((hθ _).2).trans
      (Finset.single_le_sum (f := β) (fun j _ => hβ j) (Finset.mem_univ p.1))

end Pointwise

variable [DecidableEq A] [Fintype J]

section Slots

variable (arcA arcB : J → A) {β θ : J → ℝ}

theorem atSlot_nonneg (f : Incidence J → ℝ) (hf : ∀ p, 0 ≤ f p) (a : A) (n : ℕ) :
    0 ≤ atSlot arcA arcB f a n := by
  unfold atSlot
  split_ifs
  · exact hf _
  · exact le_refl 0

theorem atSlot_mono (f g : Incidence J → ℝ) (hfg : ∀ p, f p ≤ g p) (a : A) (n : ℕ) :
    atSlot arcA arcB f a n ≤ atSlot arcA arcB g a n := by
  unfold atSlot
  split_ifs
  · exact hfg _
  · exact le_refl 0

theorem atSlot_le (f : Incidence J → ℝ) (c : ℝ) (hc : 0 ≤ c) (hf : ∀ p, f p ≤ c) (a : A)
    (n : ℕ) : atSlot arcA arcB f a n ≤ c := by
  unfold atSlot
  split_ifs
  · exact hf _
  · exact hc

theorem stepCost_nonneg (hβ : ∀ j, 0 ≤ β j) (hθ : InBox β θ) (a : A) (n : ℕ) :
    0 ≤ stepCost arcA arcB β θ a n := by
  unfold stepCost
  split_ifs
  · exact atSlot_nonneg arcA arcB _ (featureArc_nonneg hβ hθ) a _
  · exact le_refl 0

theorem diagCost_nonneg (hθ : InBox β θ) (a : A) (n : ℕ) : 0 ≤ diagCost arcA arcB θ a n := by
  unfold diagCost
  split_ifs
  · exact atSlot_nonneg arcA arcB _ (featureDiag_nonneg hθ) a _
  · exact le_refl 0

theorem diagCost_le_stepCost (hθ : InBox β θ) (a : A) (n : ℕ) :
    diagCost arcA arcB θ a n ≤ stepCost arcA arcB β θ a n := by
  unfold diagCost stepCost
  split_ifs
  · exact atSlot_mono arcA arcB _ _ (featureDiag_le_arc hθ) a _
  · exact le_refl 0

theorem diagCost_le_sum (hβ : ∀ j, 0 ≤ β j) (hθ : InBox β θ) (a : A) (n : ℕ) :
    diagCost arcA arcB θ a n ≤ ∑ j, β j := by
  have h0 : (0 : ℝ) ≤ ∑ j, β j := Finset.sum_nonneg fun j _ => hβ j
  unfold diagCost
  split_ifs
  · exact atSlot_le arcA arcB _ _ h0 (featureDiag_le_sum hβ hθ) a _
  · exact h0

theorem diagCost_last (θ : J → ℝ) (a : A) :
    diagCost arcA arcB θ a (chainLength arcA arcB a) = 0 := by
  unfold diagCost chainLength
  rw [if_neg (by omega)]

end Slots

variable [Fintype A] [Fintype V] [DecidableEq V]

section Box

variable (tail head : A → V) (arcA arcB : J → A) {s t : V} {α : A → ℝ} {β θ : J → ℝ} {δ H : ℝ}

omit [DecidableEq A] [Fintype V] [DecidableEq V] in
theorem Hyp.sum_α_nonneg (hyp : Hyp s t α β δ H) : 0 ≤ ∑ a, α a :=
  Finset.sum_nonneg fun a _ => hyp.α_nonneg a

omit [DecidableEq A] [Fintype V] [DecidableEq V] in
theorem Hyp.sum_β_nonneg (hyp : Hyp s t α β δ H) : 0 ≤ ∑ j, β j :=
  Finset.sum_nonneg fun j _ => hyp.β_nonneg j

omit [DecidableEq A] [Fintype V] [DecidableEq V] in
theorem Hyp.sum_β_le_H (hyp : Hyp s t α β δ H) : ∑ j, β j ≤ H := by
  have h1 := hyp.sum_α_nonneg
  have h2 := hyp.sum_β_nonneg
  have h3 := hyp.δ_pos
  have h4 := hyp.H_large
  linarith

omit [DecidableEq A] [Fintype V] [DecidableEq V] in
theorem Hyp.H_nonneg (hyp : Hyp s t α β δ H) : 0 ≤ H :=
  hyp.sum_β_nonneg.trans hyp.sum_β_le_H

omit [Fintype V] in
/-- **(C4).**  Every entry of the cost matrix is nonnegative for every scenario in the box. -/
theorem adapterCost_nonneg (hyp : Hyp s t α β δ H) (hθ : InBox β θ)
    (x y : Vertex V A (chainLength arcA arcB)) :
    0 ≤ adapterCost tail head arcA arcB s t α β θ δ H x y :=
  cost_nonneg tail head (chainLength arcA arcB) s t α _ _ δ H hyp.α_nonneg
    (stepCost_nonneg arcA arcB hyp.β_nonneg hθ) (diagCost_nonneg arcA arcB hθ)
    hyp.δ_pos.le hyp.H_nonneg x y

omit [Fintype V] in
/-- The diagonal entry is the smallest entry of its row, for every scenario in the box. -/
theorem adapterCost_diag_le (hyp : Hyp s t α β δ H) (hθ : InBox β θ)
    (x y : Vertex V A (chainLength arcA arcB)) :
    adapterCost tail head arcA arcB s t α β θ δ H x x
      ≤ adapterCost tail head arcA arcB s t α β θ δ H x y :=
  cost_diag_le tail head (chainLength arcA arcB) s t α _ _ δ H hyp.α_nonneg hyp.δ_pos.le
    hyp.H_nonneg (diagCost_le_stepCost arcA arcB hθ)
    (fun a n => (diagCost_le_sum arcA arcB hyp.β_nonneg hθ a n).trans hyp.sum_β_le_H)
    (fun a => (diagCost_last arcA arcB θ a).le) x y

/-- The row prices of the dual certificate: `θ j` at the first vertex of the B-feature of `j`
(internal vertex `2i + 1` of its chain), `0` at every other vertex.  They are affine in `θ`. -/
noncomputable def dualRow (arcA arcB : J → A) (θ : J → ℝ) :
    Vertex V A (chainLength arcA arcB) → ℝ
  | Sum.inl _ => 0
  | Sum.inr ⟨a, i⟩ => diagCost arcA arcB θ a i.val

omit [Fintype A] [Fintype V] in
theorem dualRow_eq_diag (s t : V) (α : A → ℝ) (β θ : J → ℝ) (δ H : ℝ)
    (x : Vertex V A (chainLength arcA arcB)) :
    dualRow arcA arcB θ x = adapterCost tail head arcA arcB s t α β θ δ H x x := by
  rcases x with u | ⟨a, i⟩
  · exact (cost_inl_self tail head (chainLength arcA arcB) s t α (stepCost arcA arcB β θ)
      (diagCost arcA arcB θ) δ H u).symm
  · exact (cost_internal_self tail head (chainLength arcA arcB) s t α (stepCost arcA arcB β θ)
      (diagCost arcA arcB θ) δ H a i).symm

/-- **Dual certificate.**  With row prices `dualRow` and column prices `0`: the dual
constraints hold for all pairs, with equality on the diagonal, and the dual objective equals the
cost of the identity. -/
theorem dual_certificate (hyp : Hyp s t α β δ H) (hθ : InBox β θ) :
    (∀ x y, dualRow arcA arcB θ x + 0 ≤ adapterCost tail head arcA arcB s t α β θ δ H x y) ∧
    (∀ x, dualRow arcA arcB θ x + 0 = adapterCost tail head arcA arcB s t α β θ δ H x x) ∧
    (∑ x : Vertex V A (chainLength arcA arcB), dualRow arcA arcB θ x
        + ∑ _x : Vertex V A (chainLength arcA arcB), (0 : ℝ)
      = permCost (adapterCost tail head arcA arcB s t α β θ δ H) (Equiv.refl _)) := by
  refine ⟨fun x y => ?_, fun x => ?_, ?_⟩
  · rw [add_zero, dualRow_eq_diag tail head arcA arcB s t α β θ δ H x]
    exact adapterCost_diag_le tail head arcA arcB hyp hθ x y
  · rw [add_zero, dualRow_eq_diag tail head arcA arcB s t α β θ δ H x]
  · rw [Finset.sum_const_zero, add_zero]
    unfold permCost
    refine Finset.sum_congr rfl fun x _ => ?_
    exact dualRow_eq_diag tail head arcA arcB s t α β θ δ H x

/-- The value of a matrix `X` under the cost matrix `C`. -/
def dot {n : Type*} [Fintype n] (C X : n → n → ℝ) : ℝ := ∑ x, ∑ y, C x y * X x y

/-- **The identity is optimal** among all doubly stochastic matrices, in every scenario of the
box (weak duality with the certificate above). -/
theorem identity_optimal (hyp : Hyp s t α β δ H) (hθ : InBox β θ)
    {X : Matrix (Vertex V A (chainLength arcA arcB)) (Vertex V A (chainLength arcA arcB)) ℝ}
    (hX : X ∈ doublyStochastic ℝ (Vertex V A (chainLength arcA arcB))) :
    permCost (adapterCost tail head arcA arcB s t α β θ δ H) (Equiv.refl _)
      ≤ dot (adapterCost tail head arcA arcB s t α β θ δ H) X := by
  unfold permCost dot
  refine Finset.sum_le_sum fun x _ => ?_
  have hrow : ∑ y, X x y = 1 := sum_row_of_mem_doublyStochastic hX x
  calc adapterCost tail head arcA arcB s t α β θ δ H x ((Equiv.refl _) x)
      = adapterCost tail head arcA arcB s t α β θ δ H x x * ∑ y, X x y := by
        rw [hrow, mul_one]; rfl
    _ = ∑ y, adapterCost tail head arcA arcB s t α β θ δ H x x * X x y := Finset.mul_sum _ _ _
    _ ≤ ∑ y, adapterCost tail head arcA arcB s t α β θ δ H x y * X x y :=
        Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_right (adapterCost_diag_le tail head arcA arcB hyp hθ x y)
            (nonneg_of_mem_doublyStochastic hX)

/-- The identity costs at most `∑ β` on the box. -/
theorem identity_cost_le (hθ : InBox β θ) :
    permCost (adapterCost tail head arcA arcB s t α β θ δ H) (Equiv.refl _) ≤ ∑ j, β j := by
  rw [adapter_identity_cost]
  exact Finset.sum_le_sum fun j _ => (hθ j).2

/-- **Completion.**  A permutation that is not designated (it uses a completion entry) costs
at least `δ + ∑ α + ∑ β + 1` more than the identity. -/
theorem completion_cost (hyp : Hyp s t α β δ H) (hθ : InBox β θ)
    {σ : Equiv.Perm (Vertex V A (chainLength arcA arcB))}
    (hσ : ¬ Designated (Edge tail head (chainLength arcA arcB)) (Sum.inl s) (Sum.inl t) σ) :
    δ + ∑ a, α a + ∑ j, β j + 1
      ≤ permCost (adapterCost tail head arcA arcB s t α β θ δ H) σ
        - permCost (adapterCost tail head arcA arcB s t α β θ δ H) (Equiv.refl _) := by
  unfold Designated at hσ
  rw [not_forall] at hσ
  obtain ⟨x, hx⟩ := hσ
  rw [not_or, not_or] at hx
  have hentry : adapterCost tail head arcA arcB s t α β θ δ H x (σ x) = H :=
    cost_completion tail head (chainLength arcA arcB) s t α _ _ δ H
      (fun h => hx.1 h.symm) hx.2.1 hx.2.2
  have hge : H ≤ permCost (adapterCost tail head arcA arcB s t α β θ δ H) σ :=
    calc H = adapterCost tail head arcA arcB s t α β θ δ H x (σ x) := hentry.symm
      _ ≤ permCost (adapterCost tail head arcA arcB s t α β θ δ H) σ :=
        Finset.single_le_sum
          (f := fun x => adapterCost tail head arcA arcB s t α β θ δ H x (σ x))
          (fun z _ => adapterCost_nonneg tail head arcA arcB hyp hθ z (σ z)) (Finset.mem_univ x)
  have hid := identity_cost_le tail head arcA arcB (s := s) (t := t) (α := α) (δ := δ) (H := H) hθ
  have hH := hyp.H_large
  linarith

omit [DecidableEq A] [Fintype J] [Fintype A] [Fintype V] [DecidableEq V] in
theorem pair_bounds {β θ u v : ℝ} (hu : u = 0 ∨ u = 1) (hv : v = 0 ∨ v = 1)
    (h0 : 0 ≤ θ) (h1 : θ ≤ β) : 0 ≤ θ * u + (β - θ) * v ∧ θ * u + (β - θ) * v ≤ β := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> constructor <;> simp <;> linarith

/-- **Routes.**  A non-identity designated permutation costs between `δ` and `δ + ∑ α + ∑ β`
more than the identity. -/
theorem designated_cost_bounds (hyp : Hyp s t α β δ H) (hθ : InBox β θ) {N : ℕ}
    (rank : V → Fin N) (hA : ∀ a, rank (tail a) < rank (head a))
    {σ : Equiv.Perm (Vertex V A (chainLength arcA arcB))}
    (hσ : Designated (Edge tail head (chainLength arcA arcB)) (Sum.inl s) (Sum.inl t) σ)
    (hne : σ ≠ Equiv.refl _) :
    δ ≤ permCost (adapterCost tail head arcA arcB s t α β θ δ H) σ
        - permCost (adapterCost tail head arcA arcB s t α β θ δ H) (Equiv.refl _) ∧
    permCost (adapterCost tail head arcA arcB s t α β θ δ H) σ
        - permCost (adapterCost tail head arcA arcB s t α β θ δ H) (Equiv.refl _)
      ≤ δ + ∑ a, α a + ∑ j, β j := by
  rw [adapter_cost_route tail head arcA arcB s t α β θ δ H rank hA hyp.hst hσ hne]
  have hα0 : 0 ≤ ∑ a, α a * y tail arcA arcB σ a := Finset.sum_nonneg fun a _ => by
    rcases y_binary tail arcA arcB σ a with h | h <;> rw [h] <;> simp [hyp.α_nonneg a]
  have hα1 : ∑ a, α a * y tail arcA arcB σ a ≤ ∑ a, α a := Finset.sum_le_sum fun a _ => by
    rcases y_binary tail arcA arcB σ a with h | h <;> rw [h] <;> simp [hyp.α_nonneg a]
  have hj := fun j => pair_bounds (β := β j) (y_binary tail arcA arcB σ (arcA j))
    (y_binary tail arcA arcB σ (arcB j)) (hθ j).1 (hθ j).2
  have hβ0 : 0 ≤ ∑ j, (θ j * y tail arcA arcB σ (arcA j)
      + (β j - θ j) * y tail arcA arcB σ (arcB j)) := Finset.sum_nonneg fun j _ => (hj j).1
  have hβ1 : ∑ j, (θ j * y tail arcA arcB σ (arcA j)
      + (β j - θ j) * y tail arcA arcB σ (arcB j)) ≤ ∑ j, β j :=
    Finset.sum_le_sum fun j _ => (hj j).2
  constructor <;> linarith

/-- Every non-identity permutation costs at least `δ` more than the identity. -/
theorem perm_cost_ge (hyp : Hyp s t α β δ H) (hθ : InBox β θ) {N : ℕ}
    (rank : V → Fin N) (hA : ∀ a, rank (tail a) < rank (head a))
    {σ : Equiv.Perm (Vertex V A (chainLength arcA arcB))} (hne : σ ≠ Equiv.refl _) :
    δ ≤ permCost (adapterCost tail head arcA arcB s t α β θ δ H) σ
        - permCost (adapterCost tail head arcA arcB s t α β θ δ H) (Equiv.refl _) := by
  by_cases hσ : Designated (Edge tail head (chainLength arcA arcB)) (Sum.inl s) (Sum.inl t) σ
  · exact (designated_cost_bounds tail head arcA arcB hyp hθ rank hA hσ hne).1
  · have h := completion_cost tail head arcA arcB hyp hθ hσ
    have h1 := hyp.sum_α_nonneg
    have h2 := hyp.sum_β_nonneg
    linarith

end Box

end Adapter
end DagCycleAssignment
