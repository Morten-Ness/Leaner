import Mathlib

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AddTorsor V P] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃]

variable {P P₂ P₃}

variable {k}

theorem restrict_map_restrict
    {n : ℕ} (s : Affine.Simplex k P n) (f : P →ᵃ[k] P₂) (hf : Function.Injective f)
    (S₁ : AffineSubspace k P) (S₂ : AffineSubspace k P₂)
    (hS₁ : affineSpan k (Set.range s.points) ≤ S₁) (hfS : AffineSubspace.map f S₁ ≤ S₂) :
    letI := Nonempty.map (AffineSubspace.inclusion hS₁) inferInstance
    letI := Nonempty.map (AffineSubspace.inclusion hfS) inferInstance
    (s.restrict S₁ hS₁).map (f.restrict hfS) (AffineMap.restrict.injective hf _) =
      (s.map f hf).restrict S₂ (Eq.trans_le
          (by simp [AffineSubspace.map_span, Set.range_comp])
          (AffineSubspace.map_mono f hS₁) |>.trans hfS) := by
  rfl

