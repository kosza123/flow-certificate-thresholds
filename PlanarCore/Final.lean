/-
  Integration.  One theorem whose only graph hypotheses are
  (i) `G` connected and (ii) a genus-0 rotation-system certificate `C` for `G`
  (Euler checked inside `C`); the dual and `B` are computed from `C`.
  Conclusion: `D = det(A Aᵀ) > 0`, `I_e = N/D` with `N ∈ ℤ`, and the least shared additive
  tolerance on the explicit networks A and B is `|N|/(D+|N|)` (= `|I_e|/(1+|I_e|)`).
-/
import PlanarCore.Certificate
import PlanarCore.Kirchhoff

namespace PlanarCore

open Matrix MGraph

/-- **Theorem 1 (certified form).** -/
theorem theorem1_certified {n q f : ℕ} (G : MGraph n q) (hG : G.Connected) (C : RotCert G f)
    (s t : Fin (n+1)) (e : Fin q) (he : current G.redInc (redB s t) e ≠ 0) :
    0 < G.detL ∧
    current G.redInc (redB s t) e = (G.numer s t e : ℝ) / (G.detL : ℝ) ∧
    IsLeast {ε | AdmissibleTransfer
        (netA (G.oriented s t) (C.dual.reorient (fun i => current G.redInc (redB s t) i < 0)) s t)
        (netB (G.oriented s t) (C.dual.reorient (fun i => current G.redInc (redB s t) i < 0)) s t e)
        ε}
      ((|G.numer s t e| : ℝ) / ((G.detL : ℝ) + |G.numer s t e|)) := by
  refine ⟨G.detL_pos hG, G.current_eq_numer_div hG s t e, ?_⟩
  rw [← G.threshold_cramer hG s t e]
  exact G.theorem1_networks C.dual hG s t (C.H2 hG) e he

/-! ### Non-vacuity: a triangle with a pendant bridge, with an actual rotation system.
Vertices 0,1,2,3; edges e0: 0→1, e1: 1→2, e2: 2→0, e3: 0→3 (bridge).
Rotation at 0: (0,f) → (3,f) → (2,t) → (0,f); at 1: (0,t) ↔ (1,f); at 2: (1,t) ↔ (2,f);
at 3: (3,t) fixed.  Faces (orbits of φ = rot ∘ α): inner {(0,f),(1,f),(2,f)} = face 0,
outer {(0,t),(3,f),(3,t),(2,t),(1,t)} = face 1.  Euler: 4 − 4 + 2 = 2.
The dual has three parallel edges 0 → 1 and a loop at face 1 (dual of the bridge). -/

/-- The triangle with a pendant edge. -/
def triG : MGraph 3 4 := ⟨![0, 1, 2, 0], ![1, 2, 0, 3]⟩

def triRot (d : Dart 4) : Dart 4 :=
  if d.2 then (![(1, false), (2, false), (0, false), (3, true)] : Fin 4 → Dart 4) d.1
  else (![(3, false), (0, true), (1, true), (2, true)] : Fin 4 → Dart 4) d.1

def triRotInv (d : Dart 4) : Dart 4 :=
  if d.2 then (![(1, false), (2, false), (3, false), (3, true)] : Fin 4 → Dart 4) d.1
  else (![(2, true), (0, true), (1, true), (0, false)] : Fin 4 → Dart 4) d.1

def triFace (d : Dart 4) : Fin 2 := if d.2 then 1 else if d.1 = 3 then 1 else 0

/-- The certificate, all conditions checked by `decide`. -/
def triCert : RotCert triG 1 where
  rot := triRot
  rotInv := triRotInv
  left_inv := by decide
  right_inv := by decide
  face := triFace
  rot_vert := by decide
  face_phi := by decide
  vert_exact := by decide
  face_exact := by decide
  face_surj := by decide
  euler := by norm_num

theorem triG_connected : triG.Connected := by
  apply MGraph.connected_of_root
  intro v
  fin_cases v
  · exact .refl
  · exact .single ⟨0, Or.inl ⟨rfl, rfl⟩⟩
  · exact .single ⟨2, Or.inr ⟨rfl, rfl⟩⟩
  · exact .single ⟨3, Or.inl ⟨rfl, rfl⟩⟩

/-- Unit current from 0 to 3 on the bridge e3 is 1 (from Kirchhoff's current law at 3). -/
theorem triG_current : current triG.redInc (redB 0 3) 3 = 1 := by
  have h := triG.kcl triG_connected 0 3 3
  simp [MGraph.div, MGraph.inc, MGraph.bvec, triG, Fin.sum_univ_four] at h
  exact h

/-- `theorem1_certified` instantiated: the certified threshold on the explicit networks is
`1/2` for the bridge. -/
theorem triG_certified_threshold :
    IsLeast {ε | AdmissibleTransfer
        (netA (triG.oriented 0 3)
          (triCert.dual.reorient (fun i => current triG.redInc (redB 0 3) i < 0)) 0 3)
        (netB (triG.oriented 0 3)
          (triCert.dual.reorient (fun i => current triG.redInc (redB 0 3) i < 0)) 0 3 3) ε}
      (1/2) := by
  obtain ⟨_, _, h⟩ := theorem1_certified triG triG_connected triCert 0 3 3
    (by rw [triG_current]; norm_num)
  rw [← triG.threshold_cramer triG_connected, triG_current] at h
  norm_num at h ⊢
  exact h

end PlanarCore
