import Mathlib

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AddTorsor V P] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃]

variable {P P₂ P₃}

variable {k}

theorem points_mem_affineSpan_faceOpposite [Nontrivial k] {n : ℕ} [NeZero n] (s : Affine.Simplex k P n)
    {i j : Fin (n + 1)} :
    s.points j ∈ affineSpan k (Set.range (s.faceOpposite i).points) ↔ j ≠ i := by
  rw [Affine.Simplex.faceOpposite, Affine.Simplex.points_mem_affineSpan_face s]
  simp

