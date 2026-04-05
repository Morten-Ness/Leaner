import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [NonAssocSemiring R]

theorem nsmul_mk (n : ℕ) (x y : R) :
    (n : QuadraticAlgebra R a b) * ⟨x, y⟩ = ⟨n * x, n * y⟩ := by
  ext <;> simp

