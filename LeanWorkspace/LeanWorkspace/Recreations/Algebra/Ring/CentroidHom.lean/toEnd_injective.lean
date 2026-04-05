import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocSemiring α]

theorem toEnd_injective : Function.Injective (CentroidHom.toEnd : CentroidHom α → AddMonoid.End α) := CentroidHom.coe_toAddMonoidHom_injective

