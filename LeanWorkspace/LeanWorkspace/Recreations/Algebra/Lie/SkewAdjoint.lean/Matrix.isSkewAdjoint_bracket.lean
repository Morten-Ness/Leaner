import Mathlib

open scoped Matrix

variable {R : Type u} {n : Type w} [CommRing R] [DecidableEq n] [Fintype n]

variable (J : Matrix n n R)

theorem Matrix.isSkewAdjoint_bracket {A B : Matrix n n R} (hA : A ∈ skewAdjointMatricesSubmodule J)
    (hB : B ∈ skewAdjointMatricesSubmodule J) : ⁅A, B⁆ ∈ skewAdjointMatricesSubmodule J := by
  simp only [mem_skewAdjointMatricesSubmodule] at *
  change ⁅A, B⁆ᵀ * J = J * (-⁅A, B⁆)
  change Aᵀ * J = J * (-A) at hA
  change Bᵀ * J = J * (-B) at hB
  rw [Matrix.lie_transpose, LieRing.of_associative_ring_bracket,
    LieRing.of_associative_ring_bracket, sub_mul, mul_assoc, mul_assoc, hA, hB, ← mul_assoc,
    ← mul_assoc, hA, hB]
  noncomm_ring

