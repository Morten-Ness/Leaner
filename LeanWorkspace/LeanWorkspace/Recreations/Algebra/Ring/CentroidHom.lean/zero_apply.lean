import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocSemiring α]

variable [Monoid M] [Monoid N] [Semiring R]

variable [DistribMulAction M α] [SMulCommClass M α α] [IsScalarTower M α α]

variable [DistribMulAction N α] [SMulCommClass N α α] [IsScalarTower N α α]

variable [Module R α] [SMulCommClass R α α] [IsScalarTower R α α]

theorem zero_apply (a : α) : (0 : CentroidHom α) a = 0 := rfl

