FAIL
import Mathlib

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AddTorsor V P] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃]

variable {P P₂ P₃}

variable {k}

theorem restrict_reindex {m n : ℕ} (s : Affine.Simplex k P n) (e : Fin (n + 1) ≃ Fin (m + 1))
    {S : AffineSubspace k P} (hS : affineSpan k (Set.range s.points) ≤ S) :
    letI := S.toAddTorsor' (by
      rcases Fin.exists_iff.mp ⟨0, by omega⟩ with ⟨i, hi⟩
      refine ⟨⟨s.points i, ?_⟩⟩
      exact hS <| by
        refine AffineSubspace.subset_affineSpan k ?_
        exact ⟨i, rfl⟩)
    True := by
  simp
