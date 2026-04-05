import Mathlib

variable {R : Type*} {a b : R}

variable [CommSemiring R]

theorem mk_eq_add_smul_omega (x y : R) :
    (⟨x, y⟩ : QuadraticAlgebra R a b) = algebraMap _ _ x + y • ω := by
  ext <;> simp

