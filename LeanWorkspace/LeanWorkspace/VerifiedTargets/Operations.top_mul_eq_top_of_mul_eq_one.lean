import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem top_mul_eq_top_of_mul_eq_one (h : N * P = 1) : ⊤ * P = ⊤ := top_unique <| by
    conv_lhs => rw [← Submodule.mul_one ⊤, ← h, ← mul_assoc]
    exact Submodule.smul_mono_left le_top

