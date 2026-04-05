import Mathlib

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {N : ι → Submodule R M}

variable [DecidableEq ι]

theorem toMatrix_directSum_collectedBasis_eq_blockDiagonal' {R M₁ M₂ : Type*} [CommSemiring R]
    [AddCommMonoid M₁] [Module R M₁] {N₁ : ι → Submodule R M₁} (h₁ : IsInternal N₁)
    [AddCommMonoid M₂] [Module R M₂] {N₂ : ι → Submodule R M₂} (h₂ : IsInternal N₂)
    {κ₁ κ₂ : ι → Type*} [∀ i, Fintype (κ₁ i)] [∀ i, Finite (κ₂ i)] [∀ i, DecidableEq (κ₁ i)]
    [Fintype ι] (b₁ : (i : ι) → Module.Basis (κ₁ i) R (N₁ i)) (b₂ : (i : ι) → Module.Basis (κ₂ i) R (N₂ i))
    {f : M₁ →ₗ[R] M₂} (hf : ∀ i, MapsTo f (N₁ i) (N₂ i)) :
    toMatrix (h₁.collectedBasis b₁) (h₂.collectedBasis b₂) f =
    Matrix.blockDiagonal' fun i ↦ toMatrix (b₁ i) (b₂ i) (f.restrict (hf i)) := by
  ext ⟨i, _⟩ ⟨j, _⟩
  simp only [toMatrix_apply, Matrix.blockDiagonal'_apply]
  rcases eq_or_ne i j with rfl | hij
  · simp [h₂.collectedBasis_repr_of_mem _ (hf _ (Subtype.mem _)), restrict_apply]
  · simp [hij, h₂.collectedBasis_repr_of_mem_ne _ hij.symm (hf _ (Subtype.mem _))]

