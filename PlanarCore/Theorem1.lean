/-
  Integration.  Theorem 1 of the paper for a connected multigraph, with
  H1 and `0 ≤ I ≤ 1` *derived* (`H1_of_connected`, `current_abs_le_one`), and the
  reorientation along the current made explicit.

  REMAINING HYPOTHESES of this intermediate file (all discharged later: the networks in
  Network.lean, H2 in Certificate.lean, the integer form in Kirchhoff.lean):
  * `H2 : ∀ z, B *ᵥ z = 0 ↔ ∃ y, z = G.redIncᵀ *ᵥ y` (planar duality + Euler; `B` is the
    reduced dual incidence matrix, an arbitrary matrix in this file);
  * the network realisation: the circulation networks of Section 2.3 project onto `FeasA` / `FeasB`
    (this is the *definition* used by `AdmissibleNet`; the networks are not built here);
  * `hK : |I_e| = κ / T` (Kirchhoff / uniform spanning tree) for the `κ/(T+κ)` form only.
-/
import PlanarCore.Graph

namespace PlanarCore

open Matrix

namespace MGraph

variable {n q k : ℕ} (G : MGraph n q)

/-- Sign of the current on each edge (`-1` where it is negative). -/
noncomputable def sgn (s t : Fin (n+1)) : Fin q → ℝ :=
  fun i => if current G.redInc (redB s t) i < 0 then -1 else 1

/-- The graph reoriented along the unit current from `s` to `t`. -/
noncomputable def oriented (s t : Fin (n+1)) : MGraph n q :=
  G.reorient (fun i => current G.redInc (redB s t) i < 0)

theorem sgn_sq (s t : Fin (n+1)) (i : Fin q) : G.sgn s t i * G.sgn s t i = 1 := by
  unfold sgn; split_ifs <;> norm_num

theorem oriented_redInc (s t : Fin (n+1)) :
    (G.oriented s t).redInc = G.redInc * diagonal (G.sgn s t) :=
  G.reorient_redInc _

theorem reorient_adj (f : Fin q → Prop) [DecidablePred f] (u v : Fin (n+1)) :
    (G.reorient f).Adj u v ↔ G.Adj u v := by
  simp only [Adj, reorient]
  constructor <;> rintro ⟨i, h⟩ <;> refine ⟨i, ?_⟩ <;> by_cases hf : f i <;> simp_all <;> tauto

/-- Reorientation keeps the graph connected. -/
theorem oriented_connected (hG : G.Connected) (s t : Fin (n+1)) : (G.oriented s t).Connected := by
  intro u v
  have h : (G.oriented s t).Adj = G.Adj := by
    funext u v; exact propext (G.reorient_adj _ u v)
  rw [h]; exact hG u v

/-- In the reoriented graph the unit current is `|I|`, edge by edge. -/
theorem oriented_current (s t : Fin (n+1)) (i : Fin q) :
    current (G.oriented s t).redInc (redB s t) i = |current G.redInc (redB s t) i| := by
  rw [oriented_redInc, reorient_current _ _ _ (G.sgn_sq s t)]
  unfold sgn
  split_ifs with h
  · rw [abs_of_neg h]; ring
  · rw [abs_of_nonneg (not_lt.1 h)]; ring

/-- `0 ≤ I ≤ 1` after reorientation: a theorem, no longer a hypothesis. -/
theorem oriented_current_mem (hG : G.Connected) (s t : Fin (n+1)) (i : Fin q) :
    0 ≤ current (G.oriented s t).redInc (redB s t) i ∧
      current (G.oriented s t).redInc (redB s t) i ≤ 1 := by
  rw [G.oriented_current]
  exact ⟨abs_nonneg _, G.current_abs_le_one hG s t i⟩

/-- **Theorem 1 (algebraic core, graph form).**  For a connected multigraph `G`, terminals
`s, t`, an observed edge `e` with nonzero current, and a dual matrix `B` satisfying H2,
the least shared additive tolerance at which the two networks (on the graph reoriented
along the current, with the dual reoriented correspondingly) return a common
observation is `|I_e| / (1 + |I_e|)`. -/
theorem theorem1_threshold (hG : G.Connected) (s t : Fin (n+1))
    (B : Matrix (Fin k) (Fin q) ℝ) (H2 : ∀ z, B *ᵥ z = 0 ↔ ∃ y, z = G.redIncᵀ *ᵥ y)
    (e : Fin q) (he : current G.redInc (redB s t) e ≠ 0) :
    IsLeast {ε | AdmissibleNet (G.oriented s t).redInc (B * diagonal (G.sgn s t)) (redB s t) e ε}
      (|current G.redInc (redB s t) e| / (1 + |current G.redInc (redB s t) e|)) := by
  have hσ := G.sgn_sq s t
  have H1' : IsUnit ((G.oriented s t).redInc * (G.oriented s t).redIncᵀ).det :=
    (G.oriented s t).H1_of_connected (G.oriented_connected hG s t)
  have H2' : ∀ z, (B * diagonal (G.sgn s t)) *ᵥ z = 0 ↔
      ∃ y, z = (G.oriented s t).redIncᵀ *ᵥ y := by
    rw [oriented_redInc]; exact reorient_H2 _ B _ hσ H2
  have hIe : 0 < current (G.oriented s t).redInc (redB s t) e := by
    rw [G.oriented_current]; exact abs_pos.2 he
  have := T1c_threshold _ _ (redB s t) e H1' H2' (G.oriented_current_mem hG s t) hIe
  rwa [G.oriented_current] at this

/-- **Theorem 1, Kirchhoff form.**  With `hK : |I_e| = κ/T`, the threshold is `κ/(T+κ)`. -/
theorem theorem1_kirchhoff (hG : G.Connected) (s t : Fin (n+1))
    (B : Matrix (Fin k) (Fin q) ℝ) (H2 : ∀ z, B *ᵥ z = 0 ↔ ∃ y, z = G.redIncᵀ *ᵥ y)
    (e : Fin q) (κ T : ℕ) (hκ : 0 < κ) (hT : 0 < T)
    (hK : |current G.redInc (redB s t) e| = (κ:ℝ) / T) :
    IsLeast {ε | AdmissibleNet (G.oriented s t).redInc (B * diagonal (G.sgn s t)) (redB s t) e ε}
      ((κ:ℝ) / (T + κ)) := by
  have hTpos : (0:ℝ) < T := by exact_mod_cast hT
  have hκpos : (0:ℝ) < κ := by exact_mod_cast hκ
  have he : current G.redInc (redB s t) e ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hK; have := div_pos hκpos hTpos; linarith
  rw [← kirchhoff_form _ κ T hT hK]
  exact G.theorem1_threshold hG s t B H2 e he

end MGraph

end PlanarCore
