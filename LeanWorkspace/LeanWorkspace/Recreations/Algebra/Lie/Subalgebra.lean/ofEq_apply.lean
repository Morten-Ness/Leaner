import Mathlib

variable {R : Type u} {L₁ : Type v} {L₂ : Type w}

variable [CommRing R] [LieRing L₁] [LieRing L₂] [LieAlgebra R L₁] [LieAlgebra R L₂]

variable (L₁' L₁'' : LieSubalgebra R L₁) (L₂' : LieSubalgebra R L₂)

theorem ofEq_apply (L L' : LieSubalgebra R L₁) (h : (L : Set L₁) = L') (x : L) :
    (↑(LieEquiv.ofEq L L' h x) : L₁) = x := rfl

