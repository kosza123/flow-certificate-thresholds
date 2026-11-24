/-
  From a gadget to the growth bound.

  * `Gadget.comp`        gadgets compose (matrix product), so alternating different gadgets
                         is covered by iterating their composite;
  * `Gadget.ofData`      the normalized gadget `N = M' / |Q|`, `κ = Q / |Q|` of a two-port with
                         open-circuit data `S, P, Q` (`Q ≠ 0`): `det N = 1` and `|κ| = 1`;
  * `iterate_current`    the `k`-fold self-substitution is a unit-resistance network with
                         `(|E| - 1) k + 1` edges whose observed current is `± 1 / q_k`;
  * `growth_of_gadget`   lower bound `λ(N)^{1/m} ≤ L` for the Fekete limit `L`;
  * `growth_fekete`      the same, combined with `PlanarCore.T3_fekete`.

  HYPOTHESES THAT ARE NOT DERIVED HERE
  * `hbridge`: the quantity `Λ` dominates the inverse observed current of every iterated
    network.  For `Λ = Λ^face` this is the statement that the iterated networks are planar
    with co-facial ports (each copy is drawn in a thin disk around the edge it replaces).
    Planarity is not formalized.
  * the hypotheses of `PlanarCore.T3_fekete` (supermultiplicativity, `Λ ≥ 1`, an exponential
    upper bound), exactly as in `PlanarCore/Fekete.lean`.
-/
import TwoPort.Growth

open Finset Filter Topology

set_option linter.unusedSectionVars false

namespace TwoPort

/-- Composition of gadgets: the outer gadget's observed edge is replaced by the inner one. -/
def Gadget.comp (g h : Gadget) : Gadget where
  tp := g.tp.comp h.tp
  M := g.M * h.M
  κ := g.κ * h.κ
  hst := fun e => g.hst (Sum.inl.inj e)
  hunit := by
    intro i hi
    cases i with
    | inl i => exact g.hunit i.1 i.2
    | inr j => exact h.hunit j fun e => hi (congrArg Sum.inr e)
  hmob := Port.hasMob_comp g.hmob h.hmob h.hst

theorem Gadget.card_comp (g h : Gadget) :
    Fintype.card (g.comp h).tp.E = (Fintype.card g.tp.E - 1) + Fintype.card h.tp.E :=
  card_comp_edges g.tp h.tp

/-- The normalized gadget of a two-port with open-circuit data `S, P, Q`, `Q ≠ 0`. -/
noncomputable def Gadget.ofData (tp : TP) {S P Q : ℝ} (hD : tp.port.Data S P Q) (hQ : Q ≠ 0)
    (hst : tp.port.s ≠ tp.port.t) (hunit : ∀ i, i ≠ tp.port.e → tp.port.res i = 1) : Gadget where
  tp := tp
  M := |Q|⁻¹ • mobM S P Q
  κ := |Q|⁻¹ * Q
  hst := hst
  hunit := hunit
  hmob := (Port.hasMob_of_data hD (fun i hi => by rw [hunit i hi]; exact one_pos) hst).smul
    (inv_pos.2 (abs_pos.2 hQ))

theorem Gadget.ofData_det (tp : TP) {S P Q : ℝ} (hD : tp.port.Data S P Q) (hQ : Q ≠ 0)
    (hst : tp.port.s ≠ tp.port.t) (hunit : ∀ i, i ≠ tp.port.e → tp.port.res i = 1) :
    (Gadget.ofData tp hD hQ hst hunit).M.det = 1 := by
  show (|Q|⁻¹ • mobM S P Q).det = 1
  rw [Matrix.det_smul, det_mobM, Fintype.card_fin, ← sq_abs Q]
  have : |Q| ≠ 0 := abs_ne_zero.2 hQ
  field_simp

theorem Gadget.ofData_abs_κ (tp : TP) {S P Q : ℝ} (hD : tp.port.Data S P Q) (hQ : Q ≠ 0)
    (hst : tp.port.s ≠ tp.port.t) (hunit : ∀ i, i ≠ tp.port.e → tp.port.res i = 1) :
    |(Gadget.ofData tp hD hQ hst hunit).κ| = 1 := by
  show |(|Q|⁻¹ * Q)| = 1
  rw [abs_mul, abs_inv, abs_abs, inv_mul_cancel₀ (abs_ne_zero.2 hQ)]

/-- **Iterated self-substitution.**  The `k`-fold nesting of a gadget with `|κ| = 1` is a
unit-resistance network with `(|E| - 1) k + 1` edges; under unit feed at its ports it has a
solution, and in every solution the observed current has absolute value `1 / q_k`. -/
theorem iterate_current (g : Gadget) (hκ : |g.κ| = 1) (k : ℕ) :
    Fintype.card (chain (List.replicate k g)).E = (Fintype.card g.tp.E - 1) * k + 1 ∧
    (∀ i, ((chain (List.replicate k g)).port.withRes 1).res i = 1) ∧
    0 < qk g.M k ∧
    (∃ φ, ((chain (List.replicate k g)).port.withRes 1).IsSol
      (feed (chain (List.replicate k g)).port.s (chain (List.replicate k g)).port.t) φ) ∧
    ∀ φ, ((chain (List.replicate k g)).port.withRes 1).IsSol
        (feed (chain (List.replicate k g)).port.s (chain (List.replicate k g)).port.t) φ →
      |((chain (List.replicate k g)).port.withRes 1).cur φ (chain (List.replicate k g)).port.e|
        = 1 / qk g.M k := by
  have hspec := (chain_spec (List.replicate k g)).2.2.2
  obtain ⟨hd, hex, hcur⟩ := chain_current (List.replicate k g)
  simp only [List.map_replicate, List.prod_replicate, List.sum_replicate, smul_eq_mul]
    at hspec hd hcur
  refine ⟨by rw [hspec, Nat.mul_comm], chain_unit _, hd, hex, fun φ hφ => ?_⟩
  rw [hcur φ hφ, abs_div, abs_pow, hκ, one_pow, abs_of_pos hd]
  rfl

/-- **Growth bound for a gadget.**  `hbridge` says that `Λ`, evaluated at the number of edges
of the `k`-fold nesting, dominates its inverse observed current. -/
theorem growth_of_gadget (g : Gadget) (hdet : g.M.det = 1) (hpos : ∀ i j, 0 < g.M i j)
    (hκ : |g.κ| = 1) (m : ℕ) (hm : 1 ≤ m) (hcard : Fintype.card g.tp.E = m + 1)
    (Λ : ℕ → ℝ) (L : ℝ) (hLUB : IsLUB {x | ∃ n, 1 ≤ n ∧ x = Λ n ^ (1 / (n:ℝ))} L)
    (hbridge : ∀ k, ∀ φ,
      ((chain (List.replicate k g)).port.withRes 1).IsSol
        (feed (chain (List.replicate k g)).port.s (chain (List.replicate k g)).port.t) φ →
      |((chain (List.replicate k g)).port.withRes 1).cur φ
          (chain (List.replicate k g)).port.e|⁻¹
        ≤ Λ (Fintype.card (chain (List.replicate k g)).E)) :
    lam g.M ^ (1 / (m:ℝ)) ≤ L := by
  refine growth Λ L m hm hLUB hdet hpos fun k => ?_
  obtain ⟨hc, _, hq, ⟨φ, hφ⟩, hcur⟩ := iterate_current g hκ k
  have := hbridge k φ hφ
  rw [hcur φ hφ, hc, hcard] at this
  simpa [one_div, inv_inv, Nat.add_sub_cancel] using this

/-- The growth bound combined with the Fekete step of `PlanarCore`. -/
theorem growth_fekete (g : Gadget) (hdet : g.M.det = 1) (hpos : ∀ i j, 0 < g.M i j)
    (hκ : |g.κ| = 1) (m : ℕ) (hm : 1 ≤ m) (hcard : Fintype.card g.tp.E = m + 1)
    (Λ : ℕ → ℝ) (δ : ℝ)
    (h1 : ∀ n, 1 ≤ n → 1 ≤ Λ n) (hδ : ∀ n, 1 ≤ n → Λ n ≤ δ ^ n)
    (hmul : ∀ p q, 1 ≤ p → 1 ≤ q → Λ p * Λ q ≤ Λ (p + q))
    (hbridge : ∀ k, ∀ φ,
      ((chain (List.replicate k g)).port.withRes 1).IsSol
        (feed (chain (List.replicate k g)).port.s (chain (List.replicate k g)).port.t) φ →
      |((chain (List.replicate k g)).port.withRes 1).cur φ
          (chain (List.replicate k g)).port.e|⁻¹
        ≤ Λ (Fintype.card (chain (List.replicate k g)).E)) :
    ∃ L, Tendsto (fun n : ℕ => Λ n ^ (1 / (n:ℝ))) atTop (𝓝 L) ∧ lam g.M ^ (1 / (m:ℝ)) ≤ L := by
  obtain ⟨L, hT, hLUB, _⟩ := PlanarCore.T3_fekete Λ δ h1 hδ hmul
  exact ⟨L, hT, growth_of_gadget g hdet hpos hκ m hm hcard Λ L hLUB hbridge⟩

end TwoPort
