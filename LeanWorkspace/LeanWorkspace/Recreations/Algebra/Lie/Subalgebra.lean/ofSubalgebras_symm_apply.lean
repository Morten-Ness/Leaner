import Mathlib

variable {R : Type u} {L₁ : Type v} {L₂ : Type w}

variable [CommRing R] [LieRing L₁] [LieRing L₂] [LieAlgebra R L₁] [LieAlgebra R L₂]

variable (L₁' L₁'' : LieSubalgebra R L₁) (L₂' : LieSubalgebra R L₂)

variable (e : L₁ ≃ₗ⁅R⁆ L₂)

theorem ofSubalgebras_symm_apply (h : L₁'.map ↑e = L₂') (x : L₂') :
    ↑((e.ofSubalgebras _ _ h).symm x) = e.symm x := rfl

