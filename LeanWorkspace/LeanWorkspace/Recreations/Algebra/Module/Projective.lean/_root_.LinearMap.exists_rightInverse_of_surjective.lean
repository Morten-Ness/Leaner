import Mathlib

variable {R : Type*} [Semiring R] {P : Type*} [AddCommMonoid P] [Module R P] {M : Type*}
  [AddCommMonoid M] [Module R M] {N : Type*} [AddCommMonoid N] [Module R N]

theorem _root_.LinearMap.exists_rightInverse_of_surjective [Projective R P]
    (f : M →ₗ[R] P) (hf_surj : range f = ⊤) : ∃ g : P →ₗ[R] M, f ∘ₗ g = LinearMap.id := Module.projective_lifting_property f (.id : P →ₗ[R] P) (LinearMap.range_eq_top.1 hf_surj)

