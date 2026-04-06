FAIL
import Mathlib

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AddTorsor V P] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃]

variable {P P₂ P₃}

variable {k}

theorem restrict_map_inclusion {n : ℕ} (s : Affine.Simplex k P n)
    (S₁ S₂ : AffineSubspace k P) (hS₁) (hS₂ : S₁ ≤ S₂) :
    letI := hS₁
    letI := hS₂
    ∀ h₁ : affineSpan k (Set.range s.points) ≤ S₁,
      Affine.Simplex.map
          ⟨AffineSubspace.inclusion hS₂, by
            intro x y h
            exact Subtype.ext h⟩
          (s.restrict S₁ h₁) =
        s.restrict S₂ (le_trans h₁ hS₂) := by
  intro h₁
  ext i
  rfl
