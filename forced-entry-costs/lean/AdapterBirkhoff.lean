import AdapterBounds
import Mathlib.Analysis.Convex.Birkhoff

/-!
# Fractional assignments: uniqueness of the optimum and the forced face

Uses the Birkhoff–von Neumann theorem of Mathlib
(`exists_eq_sum_perm_of_mem_doublyStochastic`): a doubly stochastic matrix is a convex
combination of permutation matrices.

General facts, for any finite index type and any cost matrix `C`:

* `dot_permMatrix`, `dot_combination` : the value of a convex combination of permutation
  matrices is the average of the permutation costs;
* `dot_gt_of_ne_one` : if every non-identity permutation costs at least `c > 0` more than the
  identity, then every doubly stochastic matrix other than the identity matrix costs strictly
  more than the identity;
* `exists_perm_le_of_entry_one` : if a doubly stochastic matrix `X` has the entry
  `X i₀ j₀ = 1`, then some permutation `σ` with `σ i₀ = j₀` costs at most as much as `X`.

For the adapter:

* `identity_unique_optimal` : the identity matrix is the unique optimum over all doubly
  stochastic matrices, for every scenario in the box.
-/

namespace DagCycleAssignment
namespace Adapter

open Finset Subdivision

section General

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
theorem permMatrix_entry (σ : Equiv.Perm n) (x y : n) :
    Equiv.Perm.permMatrix ℝ σ x y = if σ x = y then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

omit [Fintype n] in
theorem permMatrix_refl : Equiv.Perm.permMatrix ℝ (Equiv.refl n) = 1 := by
  simp [Equiv.Perm.permMatrix]

/-- The value of a permutation matrix is the cost of the permutation. -/
theorem dot_permMatrix (C : n → n → ℝ) (σ : Equiv.Perm n) :
    dot C (Equiv.Perm.permMatrix ℝ σ) = ∑ x, C x (σ x) := by
  unfold dot
  refine Finset.sum_congr rfl fun x _ => ?_
  have h : ∀ y, C x y * Equiv.Perm.permMatrix ℝ σ x y = if σ x = y then C x y else 0 := by
    intro y
    rw [permMatrix_entry]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun y _ => h y), Finset.sum_ite_eq univ (σ x) (fun y => C x y),
    if_pos (Finset.mem_univ _)]

/-- The value of a combination of permutation matrices. -/
theorem dot_combination (C : n → n → ℝ) (w : Equiv.Perm n → ℝ) :
    dot C (∑ σ, w σ • Equiv.Perm.permMatrix ℝ σ) = ∑ σ, w σ * ∑ x, C x (σ x) := by
  have e : ∀ x y, (∑ σ, w σ • Equiv.Perm.permMatrix ℝ σ) x y
      = ∑ σ, w σ * Equiv.Perm.permMatrix ℝ σ x y := by
    intro x y
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul]
  have h : dot C (∑ σ, w σ • Equiv.Perm.permMatrix ℝ σ)
      = ∑ σ, w σ * dot C (Equiv.Perm.permMatrix ℝ σ) := by
    unfold dot
    simp only [e, Finset.mul_sum]
    symm
    calc ∑ σ, ∑ x, ∑ y, w σ * (C x y * Equiv.Perm.permMatrix ℝ σ x y)
        = ∑ x, ∑ σ, ∑ y, w σ * (C x y * Equiv.Perm.permMatrix ℝ σ x y) := Finset.sum_comm
      _ = ∑ x, ∑ y, ∑ σ, w σ * (C x y * Equiv.Perm.permMatrix ℝ σ x y) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = ∑ x, ∑ y, ∑ σ, C x y * (w σ * Equiv.Perm.permMatrix ℝ σ x y) := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
            Finset.sum_congr rfl fun σ _ => ?_
          ring
  rw [h]
  exact Finset.sum_congr rfl fun σ _ => by rw [dot_permMatrix]

/-- If every non-identity permutation costs at least `c > 0` more than the identity, then every
doubly stochastic matrix other than the identity matrix costs strictly more than the identity. -/
theorem dot_gt_of_ne_one (C : n → n → ℝ) (c : ℝ) (hc : 0 < c)
    (hperm : ∀ σ : Equiv.Perm n, σ ≠ Equiv.refl n → c ≤ ∑ x, C x (σ x) - ∑ x, C x x)
    {X : Matrix n n ℝ} (hX : X ∈ doublyStochastic ℝ n) (hne : X ≠ 1) :
    ∑ x, C x x < dot C X := by
  obtain ⟨w, hw0, hw1, hwX⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hX
  have hex : ∃ σ₀, σ₀ ≠ Equiv.refl n ∧ 0 < w σ₀ := by
    by_contra hcon
    apply hne
    have hz : ∀ σ, σ ≠ Equiv.refl n → w σ = 0 := by
      intro σ hσ
      by_contra h
      exact hcon ⟨σ, hσ, lt_of_le_of_ne (hw0 σ) (Ne.symm h)⟩
    have h1 : w (Equiv.refl n) = 1 := by
      rw [← hw1]
      symm
      exact Finset.sum_eq_single (Equiv.refl n) (fun σ _ hσ => hz σ hσ)
        (fun h => absurd (Finset.mem_univ _) h)
    rw [← hwX, Finset.sum_eq_single (Equiv.refl n)
      (fun σ _ hσ => by rw [hz σ hσ, zero_smul]) (fun h => absurd (Finset.mem_univ _) h),
      h1, one_smul, permMatrix_refl]
  obtain ⟨σ₀, hσ₀, hw⟩ := hex
  have hid : ∑ x, C x x = ∑ σ, w σ * ∑ x, C x x := by
    rw [← Finset.sum_mul, hw1, one_mul]
  have hD : dot C X = ∑ σ, w σ * ∑ x, C x (σ x) := by
    rw [← hwX, dot_combination]
  rw [hD, hid, ← sub_pos, ← Finset.sum_sub_distrib]
  apply Finset.sum_pos'
  · intro σ _
    rw [← mul_sub]
    by_cases hσ : σ = Equiv.refl n
    · subst hσ
      simp
    · exact mul_nonneg (hw0 σ) (hc.le.trans (hperm σ hσ))
  · refine ⟨σ₀, Finset.mem_univ _, ?_⟩
    rw [← mul_sub]
    exact mul_pos hw (lt_of_lt_of_le hc (hperm σ₀ hσ₀))

/-- **The forced face.**  If a doubly stochastic matrix `X` has `X i₀ j₀ = 1`, then every
permutation of positive weight in a Birkhoff decomposition of `X` maps `i₀` to `j₀`, and one of
them costs at most as much as `X`. -/
theorem exists_perm_le_of_entry_one (C : n → n → ℝ) {X : Matrix n n ℝ}
    (hX : X ∈ doublyStochastic ℝ n) {i₀ j₀ : n} (hface : X i₀ j₀ = 1) :
    ∃ σ : Equiv.Perm n, σ i₀ = j₀ ∧ ∑ x, C x (σ x) ≤ dot C X := by
  obtain ⟨w, hw0, hw1, hwX⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hX
  have hentry : X i₀ j₀ = ∑ σ, (if σ i₀ = j₀ then w σ else 0) := by
    rw [← hwX, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Matrix.smul_apply, permMatrix_entry, smul_eq_mul]
    split_ifs <;> simp
  have hzero : ∀ σ, σ i₀ ≠ j₀ → w σ = 0 := by
    have hsum : ∑ σ, (w σ - if σ i₀ = j₀ then w σ else 0) = 0 := by
      rw [Finset.sum_sub_distrib, hw1, ← hentry, hface, sub_self]
    have hnn : ∀ σ ∈ (univ : Finset (Equiv.Perm n)),
        0 ≤ w σ - (if σ i₀ = j₀ then w σ else 0) := by
      intro σ _
      split_ifs <;> simp [hw0 σ]
    intro σ hσ
    have h := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum σ (Finset.mem_univ σ)
    rw [if_neg hσ, sub_zero] at h
    exact h
  have hmemS : ∀ σ, w σ ≠ 0 → σ ∈ univ.filter (fun σ : Equiv.Perm n => 0 < w σ) :=
    fun σ h => Finset.mem_filter.2 ⟨Finset.mem_univ _, lt_of_le_of_ne (hw0 σ) (Ne.symm h)⟩
  have hout : ∀ σ, σ ∉ univ.filter (fun σ : Equiv.Perm n => 0 < w σ) → w σ = 0 := by
    intro σ hσ
    by_contra h
    exact hσ (hmemS σ h)
  have hSne : (univ.filter (fun σ : Equiv.Perm n => 0 < w σ)).Nonempty := by
    by_contra hem
    rw [Finset.not_nonempty_iff_eq_empty] at hem
    have h0 : ∑ σ, w σ = 0 := Finset.sum_eq_zero fun σ _ => by
      apply hout
      rw [hem]
      exact Finset.not_mem_empty σ
    rw [hw1] at h0
    exact one_ne_zero h0
  have hD : ∑ σ ∈ univ.filter (fun σ : Equiv.Perm n => 0 < w σ), w σ * ∑ x, C x (σ x)
      = dot C X := by
    rw [← hwX, dot_combination]
    exact Finset.sum_subset (Finset.subset_univ _) (fun σ _ hσ => by rw [hout σ hσ, zero_mul])
  have hW : ∑ σ ∈ univ.filter (fun σ : Equiv.Perm n => 0 < w σ), w σ = 1 := by
    rw [← hw1]
    exact Finset.sum_subset (Finset.subset_univ _) (fun σ _ hσ => hout σ hσ)
  have hR : ∑ σ ∈ univ.filter (fun σ : Equiv.Perm n => 0 < w σ), w σ * dot C X = dot C X := by
    rw [← Finset.sum_mul, hW, one_mul]
  have hle : ∑ σ ∈ univ.filter (fun σ : Equiv.Perm n => 0 < w σ), w σ * ∑ x, C x (σ x)
      ≤ ∑ σ ∈ univ.filter (fun σ : Equiv.Perm n => 0 < w σ), w σ * dot C X := by
    rw [hR, hD]
  obtain ⟨σ, hσS, hσ⟩ := Finset.exists_le_of_sum_le hSne hle
  have hpos : 0 < w σ := (Finset.mem_filter.1 hσS).2
  refine ⟨σ, ?_, le_of_mul_le_mul_left hσ hpos⟩
  by_contra h
  exact hpos.ne' (hzero σ h)

end General

variable {V A J : Type*} [DecidableEq A] [Fintype J] [Fintype A] [Fintype V] [DecidableEq V]

/-- **Uniqueness in (C1).**  For every scenario in the box, every doubly stochastic matrix
other than the identity matrix costs strictly more than the identity. -/
theorem identity_unique_optimal (tail head : A → V) (arcA arcB : J → A) {s t : V} {α : A → ℝ}
    {β θ : J → ℝ} {δ H : ℝ} (hyp : Hyp s t α β δ H) (hθ : InBox β θ) {N : ℕ}
    (rank : V → Fin N) (hA : ∀ a, rank (tail a) < rank (head a))
    {X : Matrix (Vertex V A (chainLength arcA arcB)) (Vertex V A (chainLength arcA arcB)) ℝ}
    (hX : X ∈ doublyStochastic ℝ (Vertex V A (chainLength arcA arcB))) (hne : X ≠ 1) :
    permCost (adapterCost tail head arcA arcB s t α β θ δ H) (Equiv.refl _)
      < dot (adapterCost tail head arcA arcB s t α β θ δ H) X :=
  dot_gt_of_ne_one (adapterCost tail head arcA arcB s t α β θ δ H) δ hyp.δ_pos
    (fun _ hσ => perm_cost_ge tail head arcA arcB hyp hθ rank hA hσ) hX hne

end Adapter
end DagCycleAssignment
