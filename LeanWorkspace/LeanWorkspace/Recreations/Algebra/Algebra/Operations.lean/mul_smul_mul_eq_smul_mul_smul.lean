import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem mul_smul_mul_eq_smul_mul_smul (x y : R) : (x * y) • (M * N) = (x • M) * (y • N) := mul_smul_mul_comm x y M N

