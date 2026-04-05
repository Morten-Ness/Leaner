import Mathlib

variable {R : Type*} {a b : R}

variable [CommSemiring R]

variable {A : Type*} [Ring A] [Algebra R A]

theorem algHom_ext {f g : QuadraticAlgebra R a b →ₐ[R] A}
    (h : f ω = g ω) : f = g := by
  ext ⟨x, y⟩
  simp [QuadraticAlgebra.mk_eq_add_smul_omega, h]

