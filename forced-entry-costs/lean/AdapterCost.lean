import SubdivisionAssignment
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Costs on the subdivided graph: the cost of a designated permutation

This file puts a complete cost matrix on the vertex type of `SubdivisionAssignment` and
computes the cost of every designated permutation relative to the identity.

The matrix is defined on **all** ordered pairs of vertices:

* diagonal entries: `0` at an original vertex, `diagCost a i` at the `i`-th internal vertex of
  the chain of the arc `a`;
* the entry edge of the chain of `a`: `α a`;
* the `i`-th step of that chain: `stepCost a i`;
* the exit edge of a chain: `0`;
* the return entry `(t, s)`: `δ`;
* every other off-diagonal entry (the completion): `H`.

`permCost_designated` is derived from `Designated` and `whole_chain_forced`; no relation
between costs and routes is assumed.  The step and diagonal costs are arbitrary here; the
actual feature positions of the adapter are instantiated in `AdapterFeatures.lean`.
-/

namespace DagCycleAssignment
namespace Subdivision

open Finset

variable {V A : Type*}

/-- An edge that leaves an original vertex is the entry edge of a chain. -/
theorem edge_from_original (tail head : A → V) (length : A → ℕ)
    {x y : Vertex V A length} (h : Edge tail head length x y) :
    ∀ w, x = Sum.inl w → ∃ a, w = tail a ∧ y = internal length a 0 := by
  cases h with
  | entry a =>
      intro w hw
      exact ⟨a, (Sum.inl.inj hw).symm, rfl⟩
  | step a i =>
      intro w hw
      cases hw
  | exit a =>
      intro w hw
      cases hw

/-- The arc `a` is used by `σ`: the entry edge of its chain is selected. -/
def Used (tail : A → V) (length : A → ℕ) (σ : Equiv.Perm (Vertex V A length)) (a : A) : Prop :=
  σ (Sum.inl (tail a)) = internal length a 0

variable [DecidableEq V] [DecidableEq A]

instance usedDecidable (tail : A → V) (length : A → ℕ) (σ : Equiv.Perm (Vertex V A length))
    (a : A) : Decidable (Used tail length σ a) := by
  unfold Used
  infer_instance

/-- The complete cost matrix on the vertices of the subdivided graph. -/
def cost (tail head : A → V) (length : A → ℕ) (s t : V) (α : A → ℝ)
    (stepCost diagCost : A → ℕ → ℝ) (δ H : ℝ) :
    Vertex V A length → Vertex V A length → ℝ
  | Sum.inl u, Sum.inl v => if u = v then 0 else if u = t ∧ v = s then δ else H
  | Sum.inl u, Sum.inr ⟨a, i⟩ => if u = tail a ∧ i.val = 0 then α a else H
  | Sum.inr ⟨a, i⟩, Sum.inl v => if i.val = length a ∧ v = head a then 0 else H
  | Sum.inr ⟨a, i⟩, Sum.inr ⟨b, k⟩ =>
      if a = b then
        (if k.val = i.val then diagCost a i.val
         else if k.val = i.val + 1 then stepCost a i.val else H)
      else H

section Evaluate

variable (tail head : A → V) (length : A → ℕ) (s t : V) (α : A → ℝ)
  (stepCost diagCost : A → ℕ → ℝ) (δ H : ℝ)

theorem cost_inl_self (v : V) :
    cost tail head length s t α stepCost diagCost δ H (Sum.inl v) (Sum.inl v) = 0 := by
  simp [cost]

theorem cost_internal_self (a : A) (i : Fin (length a + 1)) :
    cost tail head length s t α stepCost diagCost δ H
      (internal length a i) (internal length a i) = diagCost a i.val := by
  simp [cost, internal]

theorem cost_entry (a : A) :
    cost tail head length s t α stepCost diagCost δ H
      (Sum.inl (tail a)) (internal length a 0) = α a := by
  simp [cost, internal]

theorem cost_step (a : A) (j : Fin (length a)) :
    cost tail head length s t α stepCost diagCost δ H
      (internal length a j.castSucc) (internal length a j.succ) = stepCost a j.val := by
  simp [cost, internal]

theorem cost_exit (a : A) :
    cost tail head length s t α stepCost diagCost δ H
      (internal length a (Fin.last (length a))) (Sum.inl (head a)) = 0 := by
  simp [cost, internal]

theorem cost_return (hst : s ≠ t) :
    cost tail head length s t α stepCost diagCost δ H (Sum.inl t) (Sum.inl s) = δ := by
  have hts : t ≠ s := fun h => hst h.symm
  simp [cost, hts]

/-- **Completion.**  Every off-diagonal entry that is neither an edge of the subdivided graph
nor the return entry `(t, s)` equals `H`. -/
theorem cost_completion {x y : Vertex V A length} (hxy : x ≠ y)
    (hE : ¬ Edge tail head length x y) (hret : ¬ (x = Sum.inl t ∧ y = Sum.inl s)) :
    cost tail head length s t α stepCost diagCost δ H x y = H := by
  rcases x with u | ⟨a, i⟩ <;> rcases y with v | ⟨b, k⟩
  · have h1 : u ≠ v := fun h => hxy (congrArg Sum.inl h)
    have h2 : ¬ (u = t ∧ v = s) := fun h => hret ⟨congrArg Sum.inl h.1, congrArg Sum.inl h.2⟩
    show (if u = v then 0 else if u = t ∧ v = s then δ else H) = H
    rw [if_neg h1, if_neg h2]
  · have h1 : ¬ (u = tail b ∧ k.val = 0) := by
      rintro ⟨rfl, hk⟩
      have hk0 : k = 0 := Fin.ext hk
      subst hk0
      exact hE (Edge.entry b)
    show (if u = tail b ∧ k.val = 0 then α b else H) = H
    rw [if_neg h1]
  · have h1 : ¬ (i.val = length a ∧ v = head a) := by
      rintro ⟨hi, rfl⟩
      have hil : i = Fin.last (length a) := Fin.ext hi
      subst hil
      exact hE (Edge.exit a)
    show (if i.val = length a ∧ v = head a then 0 else H) = H
    rw [if_neg h1]
  · by_cases hab : a = b
    · subst hab
      have h1 : k.val ≠ i.val := by
        intro h
        exact hxy (by rw [Fin.ext h])
      have h2 : k.val ≠ i.val + 1 := by
        intro h
        have hi : i.val < length a := by have := k.isLt; omega
        have hi' : i = (⟨i.val, hi⟩ : Fin (length a)).castSucc := Fin.ext rfl
        have hk' : k = (⟨i.val, hi⟩ : Fin (length a)).succ := Fin.ext h
        rw [hi', hk'] at hE
        exact hE (Edge.step a ⟨i.val, hi⟩)
      show (if a = a then (if k.val = i.val then diagCost a i.val
        else if k.val = i.val + 1 then stepCost a i.val else H) else H) = H
      rw [if_pos rfl, if_neg h1, if_neg h2]
    · show (if a = b then (if k.val = i.val then diagCost a i.val
        else if k.val = i.val + 1 then stepCost a i.val else H) else H) = H
      rw [if_neg hab]

end Evaluate

variable [Fintype V] [Fintype A]

/-- The cost of a permutation: the sum of the selected entries. -/
def permCost {length : A → ℕ} (C : Vertex V A length → Vertex V A length → ℝ)
    (σ : Equiv.Perm (Vertex V A length)) : ℝ :=
  ∑ x, C x (σ x)

section Rows

variable (tail head : A → V) (length : A → ℕ) (s t : V) (α : A → ℝ)
  (stepCost diagCost : A → ℕ → ℝ) (δ H : ℝ)

omit [Fintype V] in
/-- The selected entry in the row of an original vertex. -/
theorem cost_at_original (hst : s ≠ t) {σ : Equiv.Perm (Vertex V A length)}
    (hσ : Designated (Edge tail head length) (Sum.inl s) (Sum.inl t) σ) (v : V) :
    cost tail head length s t α stepCost diagCost δ H (Sum.inl v) (σ (Sum.inl v)) =
      (if v = t then (if σ (Sum.inl t) = Sum.inl s then δ else 0) else 0)
        + ∑ a, (if tail a = v then (if Used tail length σ a then α a else 0) else 0) := by
  rcases hσ (Sum.inl v) with hfix | hedge | hret
  · -- `v` is fixed
    have h1 : (if v = t then (if σ (Sum.inl t) = Sum.inl s then δ else 0) else 0) = 0 := by
      by_cases hv : v = t
      · rw [if_pos hv, if_neg]
        intro h
        rw [← hv, hfix] at h
        exact hst ((Sum.inl.inj h).symm.trans hv)
      · rw [if_neg hv]
    have h2 : ∀ a ∈ (univ : Finset A),
        (if tail a = v then (if Used tail length σ a then α a else 0) else 0) = 0 := by
      intro a _
      by_cases ha : tail a = v
      · rw [if_pos ha, if_neg]
        intro hu
        unfold Used at hu
        rw [ha, hfix] at hu
        cases hu
      · rw [if_neg ha]
    rw [hfix, cost_inl_self, h1, Finset.sum_eq_zero h2, add_zero]
  · -- `v` is the tail of a used arc
    obtain ⟨a, hva, hy⟩ := edge_from_original tail head length hedge v rfl
    have h1 : (if v = t then (if σ (Sum.inl t) = Sum.inl s then δ else 0) else 0) = 0 := by
      by_cases hv : v = t
      · rw [if_pos hv, if_neg]
        intro h
        rw [← hv, hy] at h
        cases h
      · rw [if_neg hv]
    have hused : Used tail length σ a := by
      unfold Used
      rw [← hva]
      exact hy
    have h2 : ∑ b, (if tail b = v then (if Used tail length σ b then α b else 0) else 0)
        = α a := by
      rw [Finset.sum_eq_single a]
      · rw [if_pos hva.symm, if_pos hused]
      · intro b _ hba
        by_cases hb : tail b = v
        · rw [if_pos hb, if_neg]
          intro hu
          unfold Used at hu
          rw [hb, hy] at hu
          exact hba (Sigma.mk.inj (Sum.inr.inj hu)).1.symm
        · rw [if_neg hb]
      · intro h
        exact absurd (Finset.mem_univ a) h
    rw [hy, h1, h2, zero_add, hva, cost_entry]
  · -- `v = t` and the return entry is selected
    have hv : v = t := Sum.inl.inj hret.1
    have hts : σ (Sum.inl t) = Sum.inl s := by
      rw [← hv]
      exact hret.2
    have h2 : ∀ a ∈ (univ : Finset A),
        (if tail a = v then (if Used tail length σ a then α a else 0) else 0) = 0 := by
      intro a _
      by_cases ha : tail a = v
      · rw [if_pos ha, if_neg]
        intro hu
        unfold Used at hu
        rw [ha, hret.2] at hu
        cases hu
      · rw [if_neg ha]
    rw [hret.2, Finset.sum_eq_zero h2, add_zero, if_pos hv, if_pos hts, hv,
      cost_return tail head length s t α stepCost diagCost δ H hst]

/-- The rows of the original vertices: the return entry and the entry edges of the used arcs. -/
theorem original_rows (hst : s ≠ t) {σ : Equiv.Perm (Vertex V A length)}
    (hσ : Designated (Edge tail head length) (Sum.inl s) (Sum.inl t) σ) :
    ∑ v, cost tail head length s t α stepCost diagCost δ H (Sum.inl v) (σ (Sum.inl v)) =
      (if σ (Sum.inl t) = Sum.inl s then δ else 0)
        + ∑ a, (if Used tail length σ a then α a else 0) := by
  have h := fun v => cost_at_original tail head length s t α stepCost diagCost δ H hst hσ v
  rw [Finset.sum_congr rfl (fun v _ => h v), Finset.sum_add_distrib,
    Finset.sum_ite_eq' univ t (fun _ => if σ (Sum.inl t) = Sum.inl s then δ else 0),
    if_pos (Finset.mem_univ t), Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_ite_eq univ (tail a) (fun _ => if Used tail length σ a then α a else 0),
    if_pos (Finset.mem_univ _)]

omit [Fintype V] [Fintype A] in
/-- The rows of the internal vertices of a used arc: all steps, then the exit. -/
theorem chain_rows_used {σ : Equiv.Perm (Vertex V A length)}
    (hσ : Designated (Edge tail head length) (Sum.inl s) (Sum.inl t) σ)
    (a : A) (hu : Used tail length σ a) :
    ∑ i : Fin (length a + 1), cost tail head length s t α stepCost diagCost δ H
        (internal length a i) (σ (internal length a i))
      = ∑ j : Fin (length a), stepCost a j.val := by
  obtain ⟨i, hi⟩ := (chain_entry_iff_any_internal_moved tail head length hσ a).mp hu
  obtain ⟨_, hstep, hexit, _⟩ := whole_chain_forced tail head length hσ a i hi
  rw [Fin.sum_univ_castSucc, hexit, cost_exit, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hstep j, cost_step]

omit [Fintype V] [Fintype A] in
/-- The rows of the internal vertices of an unused arc: the diagonal. -/
theorem chain_rows_unused {σ : Equiv.Perm (Vertex V A length)}
    (hσ : Designated (Edge tail head length) (Sum.inl s) (Sum.inl t) σ)
    (a : A) (hu : ¬ Used tail length σ a) :
    ∑ i : Fin (length a + 1), cost tail head length s t α stepCost diagCost δ H
        (internal length a i) (σ (internal length a i))
      = ∑ i : Fin (length a + 1), diagCost a i.val := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfix : σ (internal length a i) = internal length a i := by
    by_contra hm
    exact hu ((chain_entry_iff_any_internal_moved tail head length hσ a).mpr ⟨i, hm⟩)
  rw [hfix, cost_internal_self]

/-- Rows of original vertices and rows of internal vertices. -/
theorem permCost_split (σ : Equiv.Perm (Vertex V A length)) :
    permCost (cost tail head length s t α stepCost diagCost δ H) σ =
      ∑ v, cost tail head length s t α stepCost diagCost δ H (Sum.inl v) (σ (Sum.inl v))
        + ∑ a, ∑ i : Fin (length a + 1), cost tail head length s t α stepCost diagCost δ H
            (internal length a i) (σ (internal length a i)) := by
  unfold permCost
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  rfl

/-- The cost of the identity is the sum of the diagonal entries of the internal vertices. -/
theorem permCost_refl :
    permCost (cost tail head length s t α stepCost diagCost δ H) (Equiv.refl _) =
      ∑ a, ∑ i : Fin (length a + 1), diagCost a i.val := by
  rw [permCost_split]
  have h1 : ∑ v, cost tail head length s t α stepCost diagCost δ H
      (Sum.inl v) ((Equiv.refl (Vertex V A length)) (Sum.inl v)) = 0 :=
    Finset.sum_eq_zero fun v _ => cost_inl_self tail head length s t α stepCost diagCost δ H v
  rw [h1, zero_add]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  exact cost_internal_self tail head length s t α stepCost diagCost δ H a i

/-- **The cost of a designated permutation relative to the identity.**  For every designated
permutation `σ`: the return entry contributes `δ` if it is selected, and every used arc `a`
contributes its entry cost and its step costs and removes its diagonal costs. -/
theorem permCost_designated (hst : s ≠ t) {σ : Equiv.Perm (Vertex V A length)}
    (hσ : Designated (Edge tail head length) (Sum.inl s) (Sum.inl t) σ) :
    permCost (cost tail head length s t α stepCost diagCost δ H) σ
        - permCost (cost tail head length s t α stepCost diagCost δ H) (Equiv.refl _) =
      (if σ (Sum.inl t) = Sum.inl s then δ else 0)
        + ∑ a, (if Used tail length σ a then
            α a + ∑ j : Fin (length a), stepCost a j.val
              - ∑ i : Fin (length a + 1), diagCost a i.val
          else 0) := by
  have hchain : ∀ a, ∑ i : Fin (length a + 1), cost tail head length s t α stepCost diagCost δ H
        (internal length a i) (σ (internal length a i))
      = if Used tail length σ a then ∑ j : Fin (length a), stepCost a j.val
        else ∑ i : Fin (length a + 1), diagCost a i.val := by
    intro a
    by_cases hu : Used tail length σ a
    · rw [if_pos hu]
      exact chain_rows_used tail head length s t α stepCost diagCost δ H hσ a hu
    · rw [if_neg hu]
      exact chain_rows_unused tail head length s t α stepCost diagCost δ H hσ a hu
  have key : ∑ a, (if Used tail length σ a then
        α a + ∑ j : Fin (length a), stepCost a j.val - ∑ i : Fin (length a + 1), diagCost a i.val
      else 0)
      = ∑ a, (if Used tail length σ a then α a else 0)
        + ∑ a, (if Used tail length σ a then ∑ j : Fin (length a), stepCost a j.val
            else ∑ i : Fin (length a + 1), diagCost a i.val)
        - ∑ a, ∑ i : Fin (length a + 1), diagCost a i.val := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> ring
  rw [permCost_split, permCost_refl,
    original_rows tail head length s t α stepCost diagCost δ H hst hσ,
    Finset.sum_congr rfl (fun a _ => hchain a), key]
  ring

end Rows

end Subdivision
end DagCycleAssignment
