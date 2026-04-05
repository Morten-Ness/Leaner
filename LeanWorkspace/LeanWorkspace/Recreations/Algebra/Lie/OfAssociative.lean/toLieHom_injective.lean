import Mathlib

variable {A : Type v} [Ring A]

variable {R : Type u} [CommRing R] [Algebra R A]

variable {B : Type w} {C : Type w₁} [Ring B] [Ring C] [Algebra R B] [Algebra R C]

variable (f : A →ₐ[R] B) (g : B →ₐ[R] C)

theorem toLieHom_injective {f g : A →ₐ[R] B} (h : (f : A →ₗ⁅R⁆ B) = (g : A →ₗ⁅R⁆ B)) : f = g := by
  ext a; exact LieHom.congr_fun h a

