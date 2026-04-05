import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem mul_mem_smul_iff {S} [Ring S] [Algebra R S] {x : S} {p : Submodule R S} {y : S}
    (hx : x ∈ nonZeroDivisors S) :
    x * y ∈ x • p ↔ y ∈ p := by
  simp [mem_smul_pointwise_iff_exists, mul_cancel_left_mem_nonZeroDivisors hx]

