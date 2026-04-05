import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem mul_eq_map₂ : M * N = map₂ (LinearMap.mul R A) M N := le_antisymm (Submodule.mul_le.mpr fun _m hm _n ↦ apply_mem_map₂ _ hm)
    (map₂_le.mpr fun _m hm _n ↦ Submodule.mul_mem_mul hm)

