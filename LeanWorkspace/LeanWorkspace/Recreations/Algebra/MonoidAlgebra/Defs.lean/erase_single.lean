import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

theorem erase_single (m : M) (r : R) : MonoidAlgebra.erase m (single m r) = 0 := by
  simp [MonoidAlgebra.erase, MonoidAlgebra.ofCoeff, MonoidAlgebra.coeff]; rfl

