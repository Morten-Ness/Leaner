import Mathlib

variable {R : Type*}

variable {A : Type*}
  [Monoid R] [Monoid A] [MulAction R A] [SMulCommClass R A A]
  [IsScalarTower R A A] [StarMul R] [StarMul A] [StarModule R A]

theorem smul_mem_of_mem {r : R} {a : A} (hr : r ∈ unitary R) (ha : a ∈ unitary A) :
    r • a ∈ unitary A := by
  simp [Unitary.mem_iff, smul_smul, mul_smul_comm, smul_mul_assoc, hr, ha]

