import Mathlib

variable {R : Type*} {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem mul_toSubmodule_le (S T : Subalgebra R A) :
    Subalgebra.toSubmodule S * Subalgebra.toSubmodule T ≤ Subalgebra.toSubmodule (S ⊔ T) := by
  rw [Submodule.mul_le]
  intro y hy z hz
  simp only [mem_toSubmodule]
  exact mul_mem (Algebra.mem_sup_left hy) (Algebra.mem_sup_right hz)

