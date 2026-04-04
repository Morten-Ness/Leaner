import Mathlib

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AddTorsor V P] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃]

variable {P P₂ P₃}

variable {k}

theorem points_mem_affineSpan_face [Nontrivial k] {n : ℕ} (s : Affine.Simplex k P n)
    {fs : Finset (Fin (n + 1))} {m : ℕ} (h : #fs = m + 1) {i : Fin (n + 1)} :
    s.points i ∈ affineSpan k (Set.range (s.face h).points) ↔ i ∈ fs := by
  rw [Affine.Simplex.range_face_points]
  exact s.independent.mem_affineSpan_iff i fs

