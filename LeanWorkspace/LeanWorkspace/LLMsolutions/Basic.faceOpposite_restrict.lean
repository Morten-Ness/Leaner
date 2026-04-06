FAIL
import Mathlib

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AddTorsor V P] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃]

variable {P P₂ P₃}

variable {k}

theorem faceOpposite_restrict {n : ℕ} [NeZero n] (s : Affine.Simplex k P n) {S : AffineSubspace k P}
    (hS : affineSpan k (Set.range s.points) ≤ S) (i : Fin (n + 1)) :
    letI := Classical.choice S.toNonempty
    letI := S.toAddTorsor
    affineSpan k (Set.range (s.faceOpposite i).points) ≤ AffineSubspace.map S.subtype (⊤ : AffineSubspace k S) := by
  letI := Classical.choice S.toNonempty
  letI := S.toAddTorsor
  change affineSpan k (Set.range (s.faceOpposite i).points) ≤ S
  refine le_trans ?_ hS
  rw [Affine.Simplex.faceOpposite_range]
  exact affineSpan_mono (Set.range_comp_subset_range _ _)
