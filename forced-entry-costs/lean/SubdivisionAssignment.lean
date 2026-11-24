import DagCycleAssignment

/-!
# The actual fresh-chain topology of the assignment adapter

Each input arc owns a separate nonempty chain of fresh internal vertices.
The chain may have arbitrary length. Original parallel arcs remain distinct
because internal vertices carry the input arc index.
-/

namespace DagCycleAssignment
namespace Subdivision

variable {V A : Type*} {N M : ℕ}

abbrev Vertex (V A : Type*) (length : A → ℕ) :=
  V ⊕ (Σ a : A, Fin (length a + 1))

def internal (length : A → ℕ) (a : A) (i : Fin (length a + 1)) :
    Vertex V A length := Sum.inr ⟨a, i⟩

inductive Edge (tail head : A → V) (length : A → ℕ) :
    Vertex V A length → Vertex V A length → Prop
  | entry (a : A) : Edge tail head length (Sum.inl (tail a)) (internal length a 0)
  | step (a : A) (i : Fin (length a)) :
      Edge tail head length (internal length a i.castSucc) (internal length a i.succ)
  | exit (a : A) :
      Edge tail head length (internal length a (Fin.last (length a))) (Sum.inl (head a))

def naturalRank (rank : V → Fin N) (tail : A → V) (length : A → ℕ)
    (M : ℕ) : Vertex V A length → ℕ
  | Sum.inl v => (rank v).val * (M + 1)
  | Sum.inr ⟨a, i⟩ => (rank (tail a)).val * (M + 1) + i.val + 1

theorem naturalRank_bound (rank : V → Fin N) (tail : A → V)
    (length : A → ℕ) (hL : ∀ a, length a + 1 ≤ M)
    (v : Vertex V A length) : naturalRank rank tail length M v < N * (M + 1) := by
  cases v with
  | inl v =>
      have hr := (rank v).isLt
      have hm : ((rank v).val + 1) * (M + 1) ≤ N * (M + 1) :=
        Nat.mul_le_mul_right (M + 1) (by omega)
      dsimp [naturalRank]
      nlinarith
  | inr v =>
      obtain ⟨a, i⟩ := v
      have hr := (rank (tail a)).isLt
      have hi := i.isLt
      have hl := hL a
      have hm : ((rank (tail a)).val + 1) * (M + 1) ≤ N * (M + 1) :=
        Nat.mul_le_mul_right (M + 1) (by omega)
      dsimp [naturalRank]
      nlinarith

def liftedRank (rank : V → Fin N) (tail : A → V) (length : A → ℕ)
    (hL : ∀ a, length a + 1 ≤ M) (v : Vertex V A length) : Fin (N * (M + 1)) :=
  ⟨naturalRank rank tail length M v, naturalRank_bound rank tail length hL v⟩

theorem edge_increases_rank (rank : V → Fin N) (tail head : A → V)
    (length : A → ℕ) (hL : ∀ a, length a + 1 ≤ M)
    (hA : ∀ a, rank (tail a) < rank (head a))
    {u v : Vertex V A length} (h : Edge tail head length u v) :
    liftedRank rank tail length hL u < liftedRank rank tail length hL v := by
  change naturalRank rank tail length M u < naturalRank rank tail length M v
  cases h with
  | entry a => simp [naturalRank, internal]
  | step a i => simp [naturalRank, internal]
  | exit a =>
      have ha := hA a
      change (rank (tail a)).val < (rank (head a)).val at ha
      have hl := hL a
      have hm : ((rank (tail a)).val + 1) * (M + 1) ≤
          (rank (head a)).val * (M + 1) :=
        Nat.mul_le_mul_right (M + 1) (by omega)
      dsimp [naturalRank, internal]
      nlinarith

/-- Acyclicity of the expanded graph is proved from the original arc ranks.
No expanded-graph route correspondence or acyclicity premise is used. -/
theorem designated_iff_original_rank
    (rank : V → Fin N) (tail head : A → V) (length : A → ℕ)
    (hL : ∀ a, length a + 1 ≤ M)
    (hA : ∀ a, rank (tail a) < rank (head a))
    {s t : V} (hst : s ≠ t) (σ : Equiv.Perm (Vertex V A length)) :
    Designated (Edge tail head length) (Sum.inl s) (Sum.inl t) σ ↔
      σ = Equiv.refl _ ∨ ∃ P : SimplePath (Edge tail head length) (Sum.inl s) (Sum.inl t),
        P.toPerm = σ := by
  apply designated_iff_identity_or_path
    (fun h => hst (Sum.inl.inj h)) (liftedRank rank tail length hL)
  exact edge_increases_rank rank tail head length hL hA

def chainNext (head : A → V) (length : A → ℕ) (a : A)
    (i : Fin (length a + 1)) : Vertex V A length :=
  if h : i.val < length a then internal length a ⟨i.val + 1, by omega⟩
  else Sum.inl (head a)

def chainPrev (tail : A → V) (length : A → ℕ) (a : A)
    (i : Fin (length a + 1)) : Vertex V A length :=
  if i.val = 0 then Sum.inl (tail a)
  else internal length a ⟨i.val - 1, by omega⟩

theorem edge_out_internal (tail head : A → V) (length : A → ℕ)
    {u v : Vertex V A length} (h : Edge tail head length u v) :
    ∀ a i, u = internal length a i → v = chainNext head length a i := by
  cases h with
  | entry b =>
      intro a i heq
      cases heq
  | step b j =>
      intro a i heq
      obtain ⟨hab, hij⟩ := Sigma.mk.inj (Sum.inr.inj heq)
      subst a
      have hji : j.castSucc = i := eq_of_heq hij
      subst i
      simp [chainNext, j.isLt, internal, Fin.ext_iff]
  | exit b =>
      intro a i heq
      obtain ⟨hab, hij⟩ := Sigma.mk.inj (Sum.inr.inj heq)
      subst a
      have hji : Fin.last (length b) = i := eq_of_heq hij
      subst i
      simp [chainNext]

theorem edge_into_internal (tail head : A → V) (length : A → ℕ)
    {u v : Vertex V A length} (h : Edge tail head length u v) :
    ∀ a i, v = internal length a i → u = chainPrev tail length a i := by
  cases h with
  | entry b =>
      intro a i heq
      obtain ⟨hab, hij⟩ := Sigma.mk.inj (Sum.inr.inj heq)
      subst a
      have hji : (0 : Fin (length b + 1)) = i := eq_of_heq hij
      subst i
      simp [chainPrev]
  | step b j =>
      intro a i heq
      obtain ⟨hab, hij⟩ := Sigma.mk.inj (Sum.inr.inj heq)
      subst a
      have hji : j.succ = i := eq_of_heq hij
      subst i
      simp [chainPrev, internal, Fin.ext_iff]
  | exit b =>
      intro a i heq
      cases heq

theorem moved_internal_outgoing (tail head : A → V) (length : A → ℕ)
    {s t : V} {σ : Equiv.Perm (Vertex V A length)}
    (hσ : Designated (Edge tail head length) (Sum.inl s) (Sum.inl t) σ)
    (a : A) (i : Fin (length a + 1))
    (hm : σ (internal length a i) ≠ internal length a i) :
    σ (internal length a i) = chainNext head length a i := by
  rcases hσ (internal length a i) with hfix | hedge | hreturn
  · exact False.elim (hm hfix)
  · exact edge_out_internal tail head length hedge a i rfl
  · cases hreturn.1

theorem moved_internal_incoming (tail head : A → V) (length : A → ℕ)
    {s t : V} {σ : Equiv.Perm (Vertex V A length)}
    (hσ : Designated (Edge tail head length) (Sum.inl s) (Sum.inl t) σ)
    (a : A) (i : Fin (length a + 1))
    (hm : σ (internal length a i) ≠ internal length a i) :
    σ (chainPrev tail length a i) = internal length a i := by
  let u := σ.symm (internal length a i)
  have hu : σ u = internal length a i := σ.apply_symm_apply _
  rcases hσ u with hfix | hedge | hreturn
  · have hui : u = internal length a i := hfix.symm.trans hu
    exact False.elim (hm (hui ▸ hu))
  · have hpred : u = chainPrev tail length a i :=
      edge_into_internal tail head length hedge a i hu
    exact hpred ▸ hu
  · have hbad : internal length a i = Sum.inl s := hu.symm.trans hreturn.2
    cases hbad

theorem adjacent_internal_distinct (length : A → ℕ) (a : A) (i : Fin (length a)) :
    (internal length a i.castSucc : Vertex V A length) ≠ internal length a i.succ := by
  intro h
  have heq : i.castSucc = i.succ := eq_of_heq (Sigma.mk.inj (Sum.inr.inj h)).2
  have hv := congrArg Fin.val heq
  simp at hv

theorem adjacent_internal_moved_iff (tail head : A → V) (length : A → ℕ)
    {s t : V} {σ : Equiv.Perm (Vertex V A length)}
    (hσ : Designated (Edge tail head length) (Sum.inl s) (Sum.inl t) σ)
    (a : A) (i : Fin (length a)) :
    σ (internal length a i.castSucc) ≠ internal length a i.castSucc ↔
      σ (internal length a i.succ) ≠ internal length a i.succ := by
  have hne := adjacent_internal_distinct (V := V) length a i
  constructor
  · intro hm hfix
    have hedge : σ (internal length a i.castSucc) = internal length a i.succ := by
      simpa [chainNext, i.isLt] using moved_internal_outgoing tail head length hσ a i.castSucc hm
    exact hne (σ.injective (hedge.trans hfix.symm))
  · intro hm hfix
    have hedge : σ (internal length a i.castSucc) = internal length a i.succ := by
      simpa [chainPrev] using moved_internal_incoming tail head length hσ a i.succ hm
    exact hne (hfix.symm.trans hedge)

/-- Every internal vertex of one original arc has the same moved status.
This is a consequence of the fresh-chain topology and bijectivity. -/
theorem internal_moved_iff_first (tail head : A → V) (length : A → ℕ)
    {s t : V} {σ : Equiv.Perm (Vertex V A length)}
    (hσ : Designated (Edge tail head length) (Sum.inl s) (Sum.inl t) σ)
    (a : A) (i : Fin (length a + 1)) :
    σ (internal length a i) ≠ internal length a i ↔
      σ (internal length a 0) ≠ internal length a 0 := by
  induction i using Fin.induction with
  | zero => exact Iff.rfl
  | succ i ih =>
      exact (adjacent_internal_moved_iff tail head length hσ a i).symm.trans ih

/-- Selecting any internal feature forces the entry, every chain edge, and
the exit. This excludes partially selected original arcs. -/
theorem whole_chain_forced (tail head : A → V) (length : A → ℕ)
    {s t : V} {σ : Equiv.Perm (Vertex V A length)}
    (hσ : Designated (Edge tail head length) (Sum.inl s) (Sum.inl t) σ)
    (a : A) (i : Fin (length a + 1))
    (hm : σ (internal length a i) ≠ internal length a i) :
    σ (Sum.inl (tail a)) = internal length a 0 ∧
    (∀ j : Fin (length a), σ (internal length a j.castSucc) = internal length a j.succ) ∧
    σ (internal length a (Fin.last (length a))) = Sum.inl (head a) ∧
    ∀ j : Fin (length a + 1), σ (internal length a j) ≠ internal length a j := by
  have hzero := (internal_moved_iff_first tail head length hσ a i).mp hm
  have hall : ∀ j : Fin (length a + 1), σ (internal length a j) ≠ internal length a j :=
    fun j => (internal_moved_iff_first tail head length hσ a j).mpr hzero
  refine ⟨?_, ?_, ?_, hall⟩
  · simpa [chainPrev] using moved_internal_incoming tail head length hσ a 0 hzero
  · intro j
    simpa [chainNext, j.isLt] using moved_internal_outgoing tail head length hσ a j.castSucc (hall _)
  · simpa [chainNext] using moved_internal_outgoing tail head length hσ a (Fin.last _) (hall _)

theorem chain_entry_iff_any_internal_moved (tail head : A → V) (length : A → ℕ)
    {s t : V} {σ : Equiv.Perm (Vertex V A length)}
    (hσ : Designated (Edge tail head length) (Sum.inl s) (Sum.inl t) σ) (a : A) :
    σ (Sum.inl (tail a)) = internal length a 0 ↔
      ∃ i : Fin (length a + 1), σ (internal length a i) ≠ internal length a i := by
  constructor
  · intro hedge
    refine ⟨0, ?_⟩
    intro hfix
    have hbad := σ.injective (hedge.trans hfix.symm)
    cases hbad
  · rintro ⟨i, hm⟩
    exact (whole_chain_forced tail head length hσ a i hm).1

end Subdivision
end DagCycleAssignment

#print axioms DagCycleAssignment.Subdivision.naturalRank_bound
#print axioms DagCycleAssignment.Subdivision.edge_increases_rank
#print axioms DagCycleAssignment.Subdivision.designated_iff_original_rank
#print axioms DagCycleAssignment.Subdivision.internal_moved_iff_first
#print axioms DagCycleAssignment.Subdivision.whole_chain_forced
#print axioms DagCycleAssignment.Subdivision.chain_entry_iff_any_internal_moved
