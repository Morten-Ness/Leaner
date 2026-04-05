import Mathlib

variable {A : Type v} [Ring A]

variable {R : Type u} [CommRing R] [Algebra R A]

variable {B : Type w} {C : Type w₁} [Ring B] [Ring C] [Algebra R B] [Algebra R C]

variable (f : A →ₐ[R] B) (g : B →ₐ[R] C)

theorem toLieHom_comp : (g.comp f : A →ₗ⁅R⁆ C) = (g : B →ₗ⁅R⁆ C).comp (f : A →ₗ⁅R⁆ B) := rfl

