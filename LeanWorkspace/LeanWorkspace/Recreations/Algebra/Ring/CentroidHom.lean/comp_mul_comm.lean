import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocSemiring α]

variable [Monoid M] [Monoid N] [Semiring R]

variable [DistribMulAction M α] [SMulCommClass M α α] [IsScalarTower M α α]

variable [DistribMulAction N α] [SMulCommClass N α α] [IsScalarTower N α α]

variable [Module R α] [SMulCommClass R α α] [IsScalarTower R α α]

theorem comp_mul_comm (T S : CentroidHom α) (a b : α) : (T ∘ S) (a * b) = (S ∘ T) (a * b) := by
  simp only [Function.comp_apply]
  rw [map_mul_right, map_mul_left, ← map_mul_right, ← map_mul_left]

