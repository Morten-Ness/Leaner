import Mathlib

variable {A : Type v} [Ring A]

variable {R : Type u} [CommRing R] [Algebra R A]

variable {B : Type w} {C : Type w₁} [Ring B] [Ring C] [Algebra R B] [Algebra R C]

variable (f : A →ₐ[R] B) (g : B →ₐ[R] C)

theorem toLieHom_id : (AlgHom.id R A : A →ₗ⁅R⁆ A) = LieHom.id := rfl

