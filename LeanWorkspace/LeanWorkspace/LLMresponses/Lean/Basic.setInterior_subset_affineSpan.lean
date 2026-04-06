import Mathlib

variable {k V V₂ P P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

theorem setInterior_subset_affineSpan {I : Set k} {n : ℕ} {s : Affine.Simplex k P n} :
    s.setInterior I ⊆ affineSpan k (Set.range s.points) := by
  intro x hx
  exact s.setInterior_subset_affineSpan hx
