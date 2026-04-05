import Mathlib

variable {R : Type*} [CommSemiring R]

variable {k l m n : Type*} [DecidableEq n] [Fintype n]

theorem LinearMap.toMatrix'_mulVec (f : (n → R) →ₗ[R] m → R) (v : n → R) :
    LinearMap.toMatrix' f *ᵥ v = f v := by
  rw [← toLin'_apply, toLin'_toMatrix']

