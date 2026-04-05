import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocSemiring α]

theorem coe_toAddMonoidHom_injective : Function.Injective ((↑) : CentroidHom α → α →+ α) := fun _f _g h => CentroidHom.ext fun a ↦
    haveI := DFunLike.congr_fun h a
    this

