import Mathlib

variable {k V V₂ P P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [PartialOrder k]

theorem closedInterior_subset_affineSpan {n : ℕ} {s : Affine.Simplex k P n} :
    s.closedInterior ⊆ affineSpan k (Set.range s.points) := by
  rintro p ⟨w, hw, hi, rfl⟩
  exact affineCombination_mem_affineSpan_of_nonempty hw _

