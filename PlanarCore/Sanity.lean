/-
  Non-vacuity check: the hypotheses of `theorem1_threshold` are satisfiable.
  Graph: one edge `0 → 1`; dual matrix with no rows (a tree has no faces besides the outer one).
-/
import PlanarCore.Network

namespace PlanarCore

open Matrix MGraph

/-- One edge from vertex `0` to vertex `1`. -/
def singleEdge : MGraph 1 1 := ⟨fun _ => 0, fun _ => 1⟩

theorem singleEdge_connected : singleEdge.Connected := by
  have h01 : singleEdge.Adj 0 1 := ⟨0, Or.inl ⟨rfl, rfl⟩⟩
  have h10 : singleEdge.Adj 1 0 := ⟨0, Or.inr ⟨rfl, rfl⟩⟩
  intro u v
  fin_cases u <;> fin_cases v
  · exact .refl
  · exact .single h01
  · exact .single h10
  · exact .refl

/-- The unit current on the single edge is `1` (from Kirchhoff's current law). -/
theorem singleEdge_current : current singleEdge.redInc (redB 0 1) 0 = 1 := by
  have h := singleEdge.kcl singleEdge_connected 0 1 1
  simp [MGraph.div, MGraph.inc, MGraph.bvec, singleEdge] at h
  exact h

theorem singleEdge_H2 :
    ∀ z, (0 : Matrix (Fin 0) (Fin 1) ℝ) *ᵥ z = 0 ↔ ∃ y, z = singleEdge.redIncᵀ *ᵥ y := by
  intro z
  refine ⟨fun _ => ⟨fun _ => - z 0, ?_⟩, fun _ => Subsingleton.elim _ _⟩
  ext i; fin_cases i
  rw [singleEdge.redInc_transpose_mulVec]
  simp [singleEdge]
  rw [show (1 : Fin 2) = Fin.succ 0 from rfl, MGraph.ext_succ]
  ring

/-- `theorem1_threshold` instantiated: the threshold of the single edge is `1/2`. -/
theorem singleEdge_threshold :
    IsLeast {ε | AdmissibleNet (singleEdge.oriented 0 1).redInc
      ((0 : Matrix (Fin 0) (Fin 1) ℝ) * diagonal (singleEdge.sgn 0 1)) (redB 0 1) 0 ε} (1/2) := by
  have := singleEdge.theorem1_threshold singleEdge_connected 0 1 0 singleEdge_H2 0
    (by rw [singleEdge_current]; norm_num)
  rw [singleEdge_current] at this
  norm_num at this ⊢
  exact this

/-- Dual of the single edge: one face, and the dual edge is a loop at it (dual of a bridge). -/
def singleEdgeDual : MGraph 0 1 := ⟨fun _ => 0, fun _ => 0⟩

theorem singleEdgeDual_H2 :
    ∀ z, singleEdgeDual.redInc *ᵥ z = 0 ↔ ∃ y, z = singleEdge.redIncᵀ *ᵥ y := by
  intro z
  have h := singleEdge_H2 z
  have hl : singleEdgeDual.redInc *ᵥ z = 0 ↔ (0 : Matrix (Fin 0) (Fin 1) ℝ) *ᵥ z = 0 :=
    ⟨fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
  rw [hl]; exact h

/-- `theorem1_networks` instantiated on the explicit networks (primal edge 0→1, dual loop):
the threshold is `1/2`. -/
theorem singleEdge_networks_threshold :
    IsLeast {ε | AdmissibleTransfer
        (netA (singleEdge.oriented 0 1)
          (singleEdgeDual.reorient (fun i => current singleEdge.redInc (redB 0 1) i < 0)) 0 1)
        (netB (singleEdge.oriented 0 1)
          (singleEdgeDual.reorient (fun i => current singleEdge.redInc (redB 0 1) i < 0)) 0 1 0)
        ε} (1/2) := by
  have := singleEdge.theorem1_networks singleEdgeDual singleEdge_connected 0 1 singleEdgeDual_H2 0
    (by rw [singleEdge_current]; norm_num)
  rw [singleEdge_current] at this
  norm_num at this ⊢
  exact this

end PlanarCore
