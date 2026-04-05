import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem sumAlgEquiv_comp_rename_inl :
    (MvPolynomial.sumAlgEquiv R S₁ S₂).toAlgHom.comp (rename Sum.inl) =
      MvPolynomial.mapAlgHom (Algebra.ofId _ _) := by
  ext i
  simp

