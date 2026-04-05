import Mathlib

theorem lie_abelian_iff_equiv_lie_abelian {R : Type u} {L₁ : Type v} {L₂ : Type w} [CommRing R]
    [LieRing L₁] [LieRing L₂] [LieAlgebra R L₁] [LieAlgebra R L₂] (e : L₁ ≃ₗ⁅R⁆ L₂) :
    IsLieAbelian L₁ ↔ IsLieAbelian L₂ := ⟨e.symm.injective.isLieAbelian, e.injective.isLieAbelian⟩

