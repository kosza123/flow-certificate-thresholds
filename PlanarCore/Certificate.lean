/-
  H2 from a genus-0 rotation-system certificate.

  VERIFIED HERE (for certificates): given a connected multigraph `G` and a certificate
  `C : RotCert G f` (rotation of darts, face labels = orbits of φ = rot ∘ α, Euler's
  equation V − q + F = 2), the dual multigraph `C.dual` and its reduced incidence `B` are
  computed from the certificate, and
    * `A·Bᵀ = 0` (`orth`, `dual_mul_transpose`),
    * the dual is connected (`dual_connected`, derived, not assumed),
    * `ker B = range Aᵀ` (`H2`), by ranks (`H1_of_connected` for `G` and for the dual)
      and Euler.
  Bridges (zero column of `B`, dual loop), loops and parallel edges need no special case.

  CITED, NOT FORMALISED: a connected multigraph is planar iff it admits a genus-0 rotation
  system (Heffter–Edmonds–Ringel rotation principle + classification of surfaces; Euler's
  formula for plane graphs), and the plane dual of an embedding is the φ-orbit dual.
-/
import PlanarCore.Network

namespace PlanarCore

open Matrix

/-- Darts: `(i, false)` is the end of edge `i` at `src i`, `(i, true)` the end at `tgt i`. -/
abbrev Dart (q : ℕ) := Fin q × Bool

/-- The edge involution α. -/
def Dart.flip {q : ℕ} (d : Dart q) : Dart q := (d.1, !d.2)

@[simp] theorem Dart.flip_flip {q : ℕ} (d : Dart q) : d.flip.flip = d := by
  simp [Dart.flip]

namespace MGraph

variable {n q : ℕ} (G : MGraph n q)

/-- The vertex at which a dart sits. -/
def dv (d : Dart q) : Fin (n+1) := if d.2 then G.tgt d.1 else G.src d.1

theorem adj_symm {u v : Fin (n+1)} (h : G.Adj u v) : G.Adj v u := by
  obtain ⟨i, hi⟩ := h; exact ⟨i, hi.symm⟩

theorem connected_of_root (h : ∀ v, Relation.ReflTransGen G.Adj 0 v) : G.Connected := by
  have hsym : ∀ {a b}, Relation.ReflTransGen G.Adj a b → Relation.ReflTransGen G.Adj b a := by
    intro a b hab
    induction hab with
    | refl => exact .refl
    | tail _ hbc ih => exact (Relation.ReflTransGen.single (G.adj_symm hbc)).trans ih
  intro u v
  exact (hsym (h u)).trans (h v)

end MGraph

/-- **Genus-0 rotation-system certificate** for `G`, with `f + 1` faces. -/
structure RotCert {n q : ℕ} (G : MGraph n q) (f : ℕ) where
  /-- rotation of darts around each vertex -/
  rot : Dart q → Dart q
  rotInv : Dart q → Dart q
  left_inv : ∀ d, rotInv (rot d) = d
  right_inv : ∀ d, rot (rotInv d) = d
  /-- face labels -/
  face : Dart q → Fin (f+1)
  /-- `rot` stays at the vertex -/
  rot_vert : ∀ d, G.dv (rot d) = G.dv d
  /-- face labels are invariant under the face permutation φ = rot ∘ α -/
  face_phi : ∀ d, face (rot d.flip) = face d
  /-- vertex exactness: darts at one vertex form one rot-orbit -/
  vert_exact : ∀ d d', G.dv d = G.dv d' → ∃ k : Fin (2*q), rot^[(k:ℕ)] d = d'
  /-- face exactness: equal labels only within one φ-orbit -/
  face_exact : ∀ d d', face d = face d' → ∃ k : Fin (2*q), (fun x => rot x.flip)^[(k:ℕ)] d = d'
  /-- every label is a face -/
  face_surj : ∀ F, ∃ d, face d = F
  /-- genus 0: V − q + F = 2 -/
  euler : ((n:ℤ) + 1) - q + ((f:ℤ) + 1) = 2

namespace RotCert

variable {n q f : ℕ} {G : MGraph n q} (C : RotCert G f)

/-- The dual multigraph computed from the certificate: dual edge `i` goes from the face of
`(i,false)` to the face of `(i,true)`. -/
def dual : MGraph f q := ⟨fun i => C.face (i, false), fun i => C.face (i, true)⟩

/-- The rotation as a permutation. -/
def perm : Equiv.Perm (Dart q) := ⟨C.rot, C.rotInv, C.left_inv, C.right_inv⟩

theorem face_rot (d : Dart q) : C.face (C.rot d) = C.face d.flip := by
  have := C.face_phi d.flip; simpa using this

/-- **Orthogonality** of full incidences: `∑_i inc_G(v,i) · inc_dual(F,i) = 0`. -/
theorem orth (v : Fin (n+1)) (F : Fin (f+1)) : ∑ i, G.inc v i * C.dual.inc F i = 0 := by
  have step1 : ∑ i, G.inc v i * C.dual.inc F i =
      ∑ d : Dart q, (if G.dv d = v then 1 else 0) *
        ((if C.face d = F then 1 else 0) - (if C.face d.flip = F then 1 else 0)) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hd : C.dual.inc F i = (if C.face (i, false) = F then 1 else 0) -
        (if C.face (i, true) = F then 1 else 0) := rfl
    rw [hd]
    simp only [Fintype.sum_bool, MGraph.dv, Dart.flip, MGraph.inc, Bool.not_true,
      Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    ring
  have step2 : ∑ d : Dart q, (if G.dv d = v then (1:ℝ) else 0) *
      (if C.face (C.rot d) = F then 1 else 0) =
      ∑ d : Dart q, (if G.dv d = v then (1:ℝ) else 0) * (if C.face d = F then 1 else 0) := by
    have h := Equiv.sum_comp C.perm
      (fun d => (if G.dv d = v then (1:ℝ) else 0) * (if C.face d = F then 1 else 0))
    rw [← h]
    refine Finset.sum_congr rfl fun d _ => ?_
    show _ = (if G.dv (C.rot d) = v then (1:ℝ) else 0) * (if C.face (C.rot d) = F then 1 else 0)
    rw [C.rot_vert]
  rw [step1]
  simp_rw [← C.face_rot, mul_sub, Finset.sum_sub_distrib, step2, sub_self]

/-- Reduced orthogonality `B Aᵀ = 0`. -/
theorem dual_mul_transpose : C.dual.redInc * G.redIncᵀ = 0 := by
  ext k j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  simp only [MGraph.redInc, Matrix.transpose_apply]
  rw [← C.orth j.succ k.succ]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-! ### Dual connectivity, derived from the certificate and the connectivity of `G` -/

theorem dual_adj_flip (d : Dart q) : C.dual.Adj (C.face d) (C.face d.flip) := by
  rcases d with ⟨i, b⟩
  cases b
  · exact ⟨i, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨i, Or.inr ⟨rfl, rfl⟩⟩

theorem reach_rot (d : Dart q) :
    Relation.ReflTransGen C.dual.Adj (C.face d) (C.face (C.rot d)) := by
  rw [C.face_rot]; exact .single (C.dual_adj_flip d)

theorem reach_iter (k : ℕ) (d : Dart q) :
    Relation.ReflTransGen C.dual.Adj (C.face d) (C.face (C.rot^[k] d)) := by
  induction k with
  | zero => exact .refl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (C.reach_rot _)

theorem reach_same_vertex (d d' : Dart q) (h : G.dv d = G.dv d') :
    Relation.ReflTransGen C.dual.Adj (C.face d) (C.face d') := by
  obtain ⟨k, hk⟩ := C.vert_exact d d' h
  rw [← hk]; exact C.reach_iter _ _

theorem reach_all (hG : G.Connected) (d d' : Dart q) :
    Relation.ReflTransGen C.dual.Adj (C.face d) (C.face d') := by
  suffices ∀ v, ∀ d', G.dv d' = v → Relation.ReflTransGen C.dual.Adj (C.face d) (C.face d') from
    this _ d' rfl
  intro v
  induction hG (G.dv d) v with
  | refl => intro d' h; exact C.reach_same_vertex d d' h.symm
  | tail _ hadj ih =>
    intro d' hd'
    obtain ⟨i, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩ := hadj
    · have h1 := ih (i, false) (by simp [MGraph.dv, hs])
      have h2 : Relation.ReflTransGen C.dual.Adj (C.face (i, false)) (C.face (i, true)) :=
        .single (C.dual_adj_flip (i, false))
      have h3 := C.reach_same_vertex (i, true) d' (by rw [hd']; simp [MGraph.dv, ht])
      exact (h1.trans h2).trans h3
    · have h1 := ih (i, true) (by simp [MGraph.dv, ht])
      have h2 : Relation.ReflTransGen C.dual.Adj (C.face (i, true)) (C.face (i, false)) :=
        .single (C.dual_adj_flip (i, true))
      have h3 := C.reach_same_vertex (i, false) d' (by rw [hd']; simp [MGraph.dv, hs])
      exact (h1.trans h2).trans h3

/-- **The dual computed from the certificate is connected.** -/
theorem dual_connected (hG : G.Connected) : C.dual.Connected := by
  intro F F'
  obtain ⟨d, rfl⟩ := C.face_surj F
  obtain ⟨d', rfl⟩ := C.face_surj F'
  exact C.reach_all hG d d'

/-- **H2 from the certificate**: `ker B = range Aᵀ` for `B = C.dual.redInc`, `A = G.redInc`. -/
theorem H2 (hG : G.Connected) :
    ∀ z, C.dual.redInc *ᵥ z = 0 ↔ ∃ y, z = G.redIncᵀ *ᵥ y := by
  set A := G.redInc with hA
  set B := C.dual.redInc with hB
  have H1 : IsUnit (A * Aᵀ).det := G.H1_of_connected hG
  have H1d : IsUnit (B * Bᵀ).det := C.dual.H1_of_connected (C.dual_connected hG)
  have hBA : B * Aᵀ = 0 := C.dual_mul_transpose
  set LA := Matrix.mulVecLin Aᵀ
  set LB := Matrix.mulVecLin B
  have hle : LinearMap.range LA ≤ LinearMap.ker LB := by
    rintro _ ⟨y, rfl⟩
    simp only [LinearMap.mem_ker, LA, LB, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hBA,
      Matrix.zero_mulVec]
  have hinjA : Function.Injective LA := by
    intro y1 y2 h
    have hM : Function.Injective (A * Aᵀ).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 H1)
    apply hM
    simp only [LA, Matrix.mulVecLin_apply] at h
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h]
  have hsurjB : Function.Surjective LB := by
    intro w
    refine ⟨Bᵀ *ᵥ ((B * Bᵀ)⁻¹ *ᵥ w), ?_⟩
    simp only [LB, Matrix.mulVecLin_apply]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ H1d,
      Matrix.one_mulVec]
  have hrA : Module.finrank ℝ (LinearMap.range LA) = n := by
    rw [LinearMap.finrank_range_of_inj hinjA, Module.finrank_fin_fun]
  have hrB : Module.finrank ℝ (LinearMap.ker LB) = q - f := by
    have h := LinearMap.finrank_range_add_finrank_ker LB
    rw [LinearMap.range_eq_top.2 hsurjB, finrank_top, Module.finrank_fin_fun,
      Module.finrank_fin_fun] at h
    omega
  have heu : n + f = q := by have := C.euler; omega
  have heq : LinearMap.range LA = LinearMap.ker LB :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hrA, hrB]; omega)
  intro z
  constructor
  · intro hz
    have hz' : z ∈ LinearMap.ker LB := by
      simpa [LinearMap.mem_ker, LB, Matrix.mulVecLin_apply] using hz
    rw [← heq] at hz'
    obtain ⟨y, hy⟩ := hz'
    exact ⟨y, by rw [← hy]; rfl⟩
  · rintro ⟨y, rfl⟩
    rw [Matrix.mulVec_mulVec, hBA, Matrix.zero_mulVec]

end RotCert

end PlanarCore
