/-
  Network realisation (paper, Sections 2.3 and 3).

  The two circulation networks are built explicitly on one shared topology:
  * nodes: vertex nodes `Fin (n+1)`, face nodes `Fin (d+1)`, private nodes `u_i`, `v_i`;
  * arcs (all lower bounds 0): observed `u_i → v_i` (capacity 1),
    primal connectors `src_G i → u_i`, `v_i → tgt_G i`,
    dual connectors `src_Gd i → u_i`, `v_i → tgt_Gd i`,
    hidden return arc `t → s` among the vertex nodes;
  * version A: primal connectors 1, dual 0, return 1 with cost −1;
    version B: dual connectors 1, primal 0, return 0, cost +1 on the observed arc `e`;
  * zero balance at every node.
  `FeasA` / `FeasB` are *proved* to be the projections (`projA`, `projB`); costs and optima
  are computed (`costA`, `costB`, `optA_net`, `optB_net`).
-/
import PlanarCore.Theorem1

namespace PlanarCore

open Matrix

/-- A capacitated network with arc costs; all lower bounds are 0. -/
structure Net (N α : Type) [Fintype α] where
  tail : α → N
  head : α → N
  cap : α → ℝ
  cost : α → ℝ

namespace Net

variable {N α : Type} [Fintype α] [DecidableEq N] (K : Net N α)

/-- Net outflow at node `v`. -/
def netOut (x : α → ℝ) (v : N) : ℝ :=
  ∑ a, ((if K.tail a = v then 1 else 0) - (if K.head a = v then 1 else 0)) * x a

/-- Feasible circulation: `0 ≤ x ≤ cap` and zero balance at every node. -/
def Feasible (x : α → ℝ) : Prop := (∀ a, 0 ≤ x a ∧ x a ≤ K.cap a) ∧ ∀ v, K.netOut x v = 0

def costOf (x : α → ℝ) : ℝ := ∑ a, K.cost a * x a

/-- Optimal (minimal) cost over feasible circulations. -/
noncomputable def opt : ℝ := sInf (K.costOf '' {x | K.Feasible x})

end Net

/-- Nodes: vertices ⊕ faces ⊕ `u_i` ⊕ `v_i`. -/
abbrev TNode (n d q : ℕ) := Fin (n+1) ⊕ (Fin (d+1) ⊕ (Fin q ⊕ Fin q))
/-- Arcs: observed ⊕ primal-in ⊕ primal-out ⊕ dual-in ⊕ dual-out ⊕ return. -/
abbrev TArc (q : ℕ) := Fin q ⊕ (Fin q ⊕ (Fin q ⊕ (Fin q ⊕ (Fin q ⊕ Unit))))

variable {n d q : ℕ}

section Topology

variable (G : MGraph n q) (Gd : MGraph d q) (s t : Fin (n+1))

/-- Tails of the shared topology. -/
def ttail : TArc q → TNode n d q
  | Sum.inl i => Sum.inr (Sum.inr (Sum.inl i))                              -- observed: u_i
  | Sum.inr (Sum.inl i) => Sum.inl (G.src i)                                -- primal in
  | Sum.inr (Sum.inr (Sum.inl i)) => Sum.inr (Sum.inr (Sum.inr i))          -- primal out: v_i
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl i))) => Sum.inr (Sum.inl (Gd.src i)) -- dual in
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))) => Sum.inr (Sum.inr (Sum.inr i)) -- dual out
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))) => Sum.inl t          -- return t → s

/-- Heads of the shared topology. -/
def thead : TArc q → TNode n d q
  | Sum.inl i => Sum.inr (Sum.inr (Sum.inr i))                              -- observed: v_i
  | Sum.inr (Sum.inl i) => Sum.inr (Sum.inr (Sum.inl i))                    -- primal in: u_i
  | Sum.inr (Sum.inr (Sum.inl i)) => Sum.inl (G.tgt i)                      -- primal out
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl i))) => Sum.inr (Sum.inr (Sum.inl i)) -- dual in: u_i
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))) => Sum.inr (Sum.inl (Gd.tgt i)) -- dual out
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))) => Sum.inl s          -- return t → s

/-- Capacities: observed arcs 1, primal connectors `cP`, dual connectors `cD`, return `cR`. -/
def tcap (cP cD cR : ℝ) : TArc q → ℝ
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl _) => cP
  | Sum.inr (Sum.inr (Sum.inl _)) => cP
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => cD
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))) => cD
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))) => cR

/-- Costs: observed arc `i` costs `cObs i`, the return arc `cR`, all others 0. -/
def tcost (cR : ℝ) (cObs : Fin q → ℝ) : TArc q → ℝ
  | Sum.inl i => cObs i
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))) => cR
  | _ => 0

/-- The shared topology with given capacities and costs. -/
def topo (cap cost : TArc q → ℝ) : Net (TNode n d q) (TArc q) :=
  ⟨ttail G Gd t, thead G Gd s, cap, cost⟩

/-- Version A. -/
def netA : Net (TNode n d q) (TArc q) := topo G Gd s t (tcap 1 0 1) (tcost (-1) 0)

/-- Version B, observed edge `e`. -/
def netB (e : Fin q) : Net (TNode n d q) (TArc q) :=
  topo G Gd s t (tcap 0 1 0) (tcost 0 (fun i => if i = e then 1 else 0))

/-- The observation: flows on the observed arcs. -/
def obsOf (x : TArc q → ℝ) : Fin q → ℝ := fun i => x (Sum.inl i)
/-- The hidden return flow. -/
def retOf (x : TArc q → ℝ) : ℝ := x (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))))

variable (cap cost : TArc q → ℝ) (x : TArc q → ℝ)

theorem netOut_u (j : Fin q) :
    (topo G Gd s t cap cost).netOut x (Sum.inr (Sum.inr (Sum.inl j))) =
      x (Sum.inl j) - x (Sum.inr (Sum.inl j)) - x (Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))) := by
  simp [Net.netOut, topo, ttail, thead, Fintype.sum_sum_type]
  ring

theorem netOut_v (j : Fin q) :
    (topo G Gd s t cap cost).netOut x (Sum.inr (Sum.inr (Sum.inr j))) =
      x (Sum.inr (Sum.inr (Sum.inl j))) + x (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))))
        - x (Sum.inl j) := by
  simp [Net.netOut, topo, ttail, thead, Fintype.sum_sum_type]
  ring

theorem netOut_face (φ : Fin (d+1)) :
    (topo G Gd s t cap cost).netOut x (Sum.inr (Sum.inl φ)) =
      ∑ i, (if Gd.src i = φ then 1 else 0) * x (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
      - ∑ i, (if Gd.tgt i = φ then 1 else 0) *
          x (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))) := by
  simp [Net.netOut, topo, ttail, thead, Fintype.sum_sum_type, sub_mul, ite_mul,
    Finset.sum_sub_distrib]

theorem netOut_vtx (w : Fin (n+1)) :
    (topo G Gd s t cap cost).netOut x (Sum.inl w) =
      ∑ i, (if G.src i = w then 1 else 0) * x (Sum.inr (Sum.inl i))
      - ∑ i, (if G.tgt i = w then 1 else 0) * x (Sum.inr (Sum.inr (Sum.inl i)))
      + ((if t = w then 1 else 0) - (if s = w then 1 else 0)) * retOf x := by
  simp [Net.netOut, topo, ttail, thead, retOf, Fintype.sum_sum_type, sub_mul, ite_mul,
    Finset.sum_sub_distrib]
  ring

end Topology

namespace MGraph

variable {m : ℕ} (H : MGraph m q)

theorem div_eq_sums (z : Fin q → ℝ) (w : Fin (m+1)) :
    H.div z w = ∑ i, (if H.src i = w then 1 else 0) * z i
      - ∑ i, (if H.tgt i = w then 1 else 0) * z i := by
  simp [div, inc, sub_mul, ite_mul, Finset.sum_sub_distrib]

/-- Balance at the non-reference rows plus a zero-sum target gives balance everywhere
(the reference row is redundant). -/
theorem div_full (z : Fin q → ℝ) (g : Fin (m+1) → ℝ) (hsucc : ∀ j : Fin m, H.div z j.succ = g j.succ)
    (hg : ∑ w, g w = 0) (w : Fin (m+1)) : H.div z w = g w := by
  have hd := H.sum_div z
  rw [Fin.sum_univ_succ] at hd hg
  simp only [hsucc] at hd
  refine Fin.cases ?_ (fun j => hsucc j) w
  linarith

theorem sum_bvec (s t : Fin (m+1)) : ∑ w, bvec s t w = 0 := by
  simp [bvec, Finset.sum_sub_distrib]

end MGraph

theorem ite_swap_eq {m : ℕ} (a w : Fin (m+1)) :
    (if a = w then (1:ℝ) else 0) = if w = a then 1 else 0 := by
  by_cases h : w = a
  · subst h; simp
  · simp [h, Ne.symm h]

section Projections

variable (G : MGraph n q) (Gd : MGraph d q) (s t : Fin (n+1))

/-- **(i)** The projection of A's feasible circulations onto (observed flows, return flow)
is exactly `FeasA G.redInc (redB s t)`. -/
theorem projA (z : Fin q → ℝ) (f : ℝ) :
    (∃ x, (netA G Gd s t).Feasible x ∧ obsOf x = z ∧ retOf x = f) ↔
      FeasA G.redInc (MGraph.redB s t) z f := by
  constructor
  · rintro ⟨x, ⟨hcap, hbal⟩, rfl, rfl⟩
    have hdin : ∀ i, x (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))) = 0 := fun i => by
      have := hcap (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
      simp only [netA, topo, tcap] at this; linarith [this.1, this.2]
    have hpin : ∀ i, x (Sum.inr (Sum.inl i)) = x (Sum.inl i) := fun i => by
      have := hbal (Sum.inr (Sum.inr (Sum.inl i)))
      rw [netA, netOut_u, hdin] at this; linarith
    have hpout : ∀ i, x (Sum.inr (Sum.inr (Sum.inl i))) = x (Sum.inl i) := fun i => by
      have := hbal (Sum.inr (Sum.inr (Sum.inr i)))
      have h2 := hcap (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))
      simp only [netA, topo, tcap] at h2
      rw [netA, netOut_v] at this; linarith [h2.1, h2.2]
    refine ⟨?_, fun i => ?_, ?_⟩
    · ext j
      have hv := hbal (Sum.inl j.succ)
      rw [netA, netOut_vtx] at hv
      simp only [hpin, hpout] at hv
      rw [MGraph.redInc_mulVec, MGraph.div_eq_sums]
      simp only [Pi.smul_apply, smul_eq_mul, MGraph.redB, MGraph.bvec, obsOf]
      rw [ite_swap_eq t, ite_swap_eq s] at hv
      linear_combination hv
    · have := hcap (Sum.inl i); simpa [netA, topo, tcap, obsOf] using this
    · have := hcap (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))))
      simpa [netA, topo, tcap, retOf] using this
  · rintro ⟨hA, hz, hf⟩
    have hdiv : ∀ w, G.div z w = f * MGraph.bvec s t w := by
      refine G.div_full z _ (fun j => ?_) (by rw [← Finset.mul_sum, MGraph.sum_bvec, mul_zero])
      rw [← MGraph.redInc_mulVec, hA]; rfl
    refine ⟨Sum.elim z (Sum.elim z (Sum.elim z (Sum.elim 0 (Sum.elim 0 (fun _ => f))))),
      ⟨?_, ?_⟩, rfl, rfl⟩
    · rintro (i | i | i | i | i | u) <;>
        simp [netA, topo, tcap, hz, hf.1, hf.2]
    · rintro (w | φ | j | j)
      · have := hdiv w
        rw [MGraph.div_eq_sums] at this
        rw [netA, netOut_vtx, ite_swap_eq t, ite_swap_eq s]
        simp only [Sum.elim_inl, Sum.elim_inr, retOf, MGraph.bvec] at this ⊢
        linear_combination this
      · rw [netA, netOut_face]; simp
      · rw [netA, netOut_u]; simp
      · rw [netA, netOut_v]; simp

/-- **(ii)** The projection of B's feasible circulations onto the observed flows is exactly
`FeasB Gd.redInc`. -/
theorem projB (e : Fin q) (z : Fin q → ℝ) :
    (∃ x, (netB G Gd s t e).Feasible x ∧ obsOf x = z) ↔ FeasB Gd.redInc z := by
  constructor
  · rintro ⟨x, ⟨hcap, hbal⟩, rfl⟩
    have hpin : ∀ i, x (Sum.inr (Sum.inl i)) = 0 := fun i => by
      have := hcap (Sum.inr (Sum.inl i))
      simp only [netB, topo, tcap] at this; linarith [this.1, this.2]
    have hdin : ∀ i, x (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))) = x (Sum.inl i) := fun i => by
      have := hbal (Sum.inr (Sum.inr (Sum.inl i)))
      rw [netB, netOut_u, hpin] at this; linarith
    have hdout : ∀ i, x (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))) = x (Sum.inl i) :=
      fun i => by
      have := hbal (Sum.inr (Sum.inr (Sum.inr i)))
      have h2 := hcap (Sum.inr (Sum.inr (Sum.inl i)))
      simp only [netB, topo, tcap] at h2
      rw [netB, netOut_v] at this; linarith [h2.1, h2.2]
    refine ⟨?_, fun i => ?_⟩
    · ext j
      have hv := hbal (Sum.inr (Sum.inl j.succ))
      rw [netB, netOut_face] at hv
      simp only [hdin, hdout] at hv
      rw [MGraph.redInc_mulVec, MGraph.div_eq_sums]
      simpa [obsOf] using hv
    · have := hcap (Sum.inl i); simpa [netB, topo, tcap, obsOf] using this
  · rintro ⟨hB, hz⟩
    have hdiv : ∀ φ, Gd.div z φ = 0 := by
      intro φ
      have := Gd.div_full z (fun _ => 0) (fun j => ?_) (by simp) φ
      · exact this
      · rw [← MGraph.redInc_mulVec, hB]; rfl
    refine ⟨Sum.elim z (Sum.elim 0 (Sum.elim 0 (Sum.elim z (Sum.elim z (fun _ => 0))))),
      ⟨?_, ?_⟩, rfl⟩
    · rintro (i | i | i | i | i | u) <;> simp [netB, topo, tcap, hz]
    · rintro (w | φ | j | j)
      · rw [netB, netOut_vtx]; simp [retOf]
      · have := hdiv φ
        rw [MGraph.div_eq_sums] at this
        rw [netB, netOut_face]
        simpa using this
      · rw [netB, netOut_u]; simp
      · rw [netB, netOut_v]; simp

/-- **(iii)** Cost of version A is `-f` (minus the return flow). -/
theorem costA (x : TArc q → ℝ) : (netA G Gd s t).costOf x = - retOf x := by
  simp [Net.costOf, netA, topo, tcost, retOf, Fintype.sum_sum_type]

/-- **(iii)** Cost of version B is `z_e`. -/
theorem costB (e : Fin q) (x : TArc q → ℝ) : (netB G Gd s t e).costOf x = obsOf x e := by
  simp [Net.costOf, netB, topo, tcost, obsOf, Fintype.sum_sum_type]

theorem costs_A : (netA G Gd s t).costOf '' {x | (netA G Gd s t).Feasible x} =
    {v | ∃ z f, FeasA G.redInc (MGraph.redB s t) z f ∧ v = -f} := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨obsOf x, retOf x, (projA G Gd s t _ _).1 ⟨x, hx, rfl, rfl⟩, costA G Gd s t x⟩
  · rintro ⟨z, f, h, rfl⟩
    obtain ⟨x, hx, -, hf⟩ := (projA G Gd s t z f).2 h
    exact ⟨x, hx, by rw [costA, hf]⟩

theorem costs_B (e : Fin q) : (netB G Gd s t e).costOf '' {x | (netB G Gd s t e).Feasible x} =
    {v | ∃ z, FeasB Gd.redInc z ∧ v = z e} := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨obsOf x, (projB G Gd s t e _).1 ⟨x, hx, rfl⟩, costB G Gd s t e x⟩
  · rintro ⟨z, h, rfl⟩
    obtain ⟨x, hx, hz⟩ := (projB G Gd s t e z).2 h
    exact ⟨x, hx, by rw [costB, hz]⟩

/-- Optimum of A is `-1` when the current is a flow with `0 ≤ I ≤ 1`. -/
theorem optA_net (H1 : IsUnit (G.redInc * G.redIncᵀ).det)
    (hI01 : ∀ i, 0 ≤ current G.redInc (MGraph.redB s t) i ∧
      current G.redInc (MGraph.redB s t) i ≤ 1) :
    (netA G Gd s t).opt = -1 := by
  rw [Net.opt, costs_A]; exact (optA _ _ H1 hI01).csInf_eq

/-- Optimum of B is `0`. -/
theorem optB_net (e : Fin q) : (netB G Gd s t e).opt = 0 := by
  rw [Net.opt, costs_B]; exact (optB _ e).csInf_eq

end Projections

/-- Shared additive tolerance on the *networks*: the two versions return circulations with
the same observation, each within `ε` of its own optimum. -/
def AdmissibleTransfer {N : Type} [DecidableEq N] (KA KB : Net N (TArc q)) (ε : ℝ) : Prop :=
  ∃ xA xB, KA.Feasible xA ∧ KB.Feasible xB ∧ obsOf xA = obsOf xB ∧
    KA.costOf xA - KA.opt ≤ ε ∧ KB.costOf xB - KB.opt ≤ ε

theorem admissibleTransfer_iff (G : MGraph n q) (Gd : MGraph d q) (s t : Fin (n+1)) (e : Fin q)
    (H1 : IsUnit (G.redInc * G.redIncᵀ).det)
    (hI01 : ∀ i, 0 ≤ current G.redInc (MGraph.redB s t) i ∧
      current G.redInc (MGraph.redB s t) i ≤ 1) (ε : ℝ) :
    AdmissibleTransfer (netA G Gd s t) (netB G Gd s t e) ε ↔
      AdmissibleNet G.redInc Gd.redInc (MGraph.redB s t) e ε := by
  rw [AdmissibleTransfer, optA_net G Gd s t H1 hI01, optB_net]
  constructor
  · rintro ⟨xA, xB, hA, hB, hobs, h1, h2⟩
    refine ⟨obsOf xA, retOf xA, (projA G Gd s t _ _).1 ⟨xA, hA, rfl, rfl⟩,
      (projB G Gd s t e _).1 ⟨xB, hB, hobs.symm⟩, ?_, ?_⟩
    · rw [costA] at h1; linarith
    · rw [costB, ← hobs] at h2; linarith
  · rintro ⟨z, f, hA, hB, h1, h2⟩
    obtain ⟨xA, hxA, hzA, hfA⟩ := (projA G Gd s t z f).2 hA
    obtain ⟨xB, hxB, hzB⟩ := (projB G Gd s t e z).2 hB
    refine ⟨xA, xB, hxA, hxB, by rw [hzA, hzB], ?_, ?_⟩
    · rw [costA, hfA]; linarith
    · rw [costB, hzB]; linarith

namespace MGraph

variable (G : MGraph n q) (Gd : MGraph d q)

/-- **(iv) Theorem 1 on the explicit networks.**  `G` connected, `Gd` any multigraph on the
same edge set whose reduced incidence satisfies H2 against `G`.  Both graphs are reoriented
along the current (a primal edge and its dual edge are reversed together).  The least shared
additive tolerance at which networks A and B return a common observation is
`|I_e|/(1+|I_e|)`. -/
theorem theorem1_networks (hG : G.Connected) (s t : Fin (n+1))
    (H2 : ∀ z, Gd.redInc *ᵥ z = 0 ↔ ∃ y, z = G.redIncᵀ *ᵥ y)
    (e : Fin q) (he : current G.redInc (redB s t) e ≠ 0) :
    IsLeast {ε | AdmissibleTransfer (netA (G.oriented s t) (Gd.reorient (fun i => current G.redInc (redB s t) i < 0)) s t)
        (netB (G.oriented s t) (Gd.reorient (fun i => current G.redInc (redB s t) i < 0)) s t e) ε}
      (|current G.redInc (redB s t) e| / (1 + |current G.redInc (redB s t) e|)) := by
  have hGd : (Gd.reorient (fun i => current G.redInc (redB s t) i < 0)).redInc = Gd.redInc * diagonal (G.sgn s t) :=
    Gd.reorient_redInc _
  have H1' := (G.oriented s t).H1_of_connected (G.oriented_connected hG s t)
  have hset : {ε | AdmissibleTransfer (netA (G.oriented s t) (Gd.reorient (fun i => current G.redInc (redB s t) i < 0)) s t)
        (netB (G.oriented s t) (Gd.reorient (fun i => current G.redInc (redB s t) i < 0)) s t e) ε} =
      {ε | AdmissibleNet (G.oriented s t).redInc (Gd.redInc * diagonal (G.sgn s t))
        (redB s t) e ε} := by
    ext ε
    exact (admissibleTransfer_iff _ _ s t e H1' (G.oriented_current_mem hG s t) ε).trans
      (by rw [hGd]; exact Iff.rfl)
  rw [hset]
  exact G.theorem1_threshold hG s t Gd.redInc H2 e he

/-- **(iv), Kirchhoff form.** -/
theorem theorem1_networks_kirchhoff (hG : G.Connected) (s t : Fin (n+1))
    (H2 : ∀ z, Gd.redInc *ᵥ z = 0 ↔ ∃ y, z = G.redIncᵀ *ᵥ y)
    (e : Fin q) (κ T : ℕ) (hκ : 0 < κ) (hT : 0 < T)
    (hK : |current G.redInc (redB s t) e| = (κ:ℝ) / T) :
    IsLeast {ε | AdmissibleTransfer (netA (G.oriented s t) (Gd.reorient (fun i => current G.redInc (redB s t) i < 0)) s t)
        (netB (G.oriented s t) (Gd.reorient (fun i => current G.redInc (redB s t) i < 0)) s t e) ε} ((κ:ℝ) / (T + κ)) := by
  have hTpos : (0:ℝ) < T := by exact_mod_cast hT
  have hκpos : (0:ℝ) < κ := by exact_mod_cast hκ
  have he : current G.redInc (redB s t) e ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hK; have := div_pos hκpos hTpos; linarith
  rw [← kirchhoff_form _ κ T hT hK]
  exact G.theorem1_networks Gd hG s t H2 e he

end MGraph

end PlanarCore
