module

public import Mathlib
public import Kenyon.Main
public import Kenyon.Sharp

/-!
# Spanning trees per edge

Wrapper of the published full proof, with independently restated definitions and conclusions.
The formalization covers the general multigraph supremum in Kenyon's 1996 question, not
the planar supremum or the exact extremizer for each fixed number of edges.
-/

@[expose] public section

open Finset

namespace PalomarKenyon

variable {V E : Type}

/-- Edge set F joins x and y by one unoriented edge. Distinct edge labels allow parallel edges; equal endpoints allow loops. -/
def Adj (src tgt : E → V) (F : Finset E) (x y : V) : Prop :=
  ∃ e ∈ F, (src e = x ∧ tgt e = y) ∨ (src e = y ∧ tgt e = x)

/-- Connectivity using edges in F. -/
def Conn (src tgt : E → V) (F : Finset E) : V → V → Prop :=
  Relation.ReflTransGen (Adj src tgt F)

/-- A spanning tree is a connected set of |V| - 1 labelled edges. -/
def IsTree [Fintype V] (src tgt : E → V) (T : Finset E) : Prop :=
  T.card + 1 = Fintype.card V ∧ ∀ x y, Conn src tgt T x y

open scoped Classical in
/-- The number of spanning trees, counted as distinct subsets of the labelled edge set. -/
noncomputable def numTrees [Fintype V] [Fintype E] (src tgt : E → V) : ℕ :=
  ((univ : Finset (Finset E)).filter fun T => IsTree src tgt T).card

/-- Strict universal upper bound for every finite multigraph with at least one edge, including disconnected graphs, loops and parallel edges. -/
theorem kenyon_bound (V E : Type) [Fintype V] [Fintype E] (src tgt : E → V)
    (hm : 0 < Fintype.card E) :
    numTrees src tgt ^ 2 * 8 ^ Fintype.card E < 27 ^ Fintype.card E := by
  exact Kenyon.kenyon_bound V E src tgt hm

/-- The equivalent real-valued inequality, as stated in the paper. -/
theorem kenyon_bound_real (V E : Type) [Fintype V] [Fintype E] (src tgt : E → V)
    (hm : 0 < Fintype.card E) :
    (numTrees src tgt : ℝ) < (27 / 8 : ℝ) ^ ((Fintype.card E : ℝ) / 2) := by
  exact Kenyon.kenyon_bound_real V E src tgt hm

/-- Every positive squared exponential base smaller than 27/8 fails on some finite multigraph with a positive number of edges. Together with the strict upper bound, this gives the nonattained supremum sqrt(27/8). -/
theorem kenyon_sharp (c : ℝ) (hc0 : 0 < c) (hc : c < 27 / 8) :
    ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E) (src tgt : E → V),
      0 < Fintype.card E ∧ c ^ Fintype.card E < (numTrees src tgt : ℝ) ^ 2 := by
  exact Kenyon.kenyon_sharp c hc0 hc

end PalomarKenyon
