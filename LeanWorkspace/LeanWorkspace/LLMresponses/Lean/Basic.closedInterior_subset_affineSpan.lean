FAIL
import Mathlib

variable {k V V₂ P P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [PartialOrder k]

theorem closedInterior_subset_affineSpan {n : ℕ} {s : Affine.Simplex k P n} :
    s.closedInterior ⊆ affineSpan k (Set.range s.points) := by
  intro x hx
  rw [Affine.Simplex.closedInterior] at hx
  rcases hx with ⟨w, rfl, -, -⟩
  exact Affine.mem_affineSpan_of_eq_weightedVSub_vadd_eq_weightedVSubOfPoint_vadd k s.points w
