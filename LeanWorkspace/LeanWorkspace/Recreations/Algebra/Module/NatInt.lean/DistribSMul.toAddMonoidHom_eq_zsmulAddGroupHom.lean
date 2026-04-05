import Mathlib

variable {R S M M₂ : Type*}

variable (M) [AddCommGroup M]

theorem DistribSMul.toAddMonoidHom_eq_zsmulAddGroupHom :
    toAddMonoidHom M = zsmulAddGroupHom := rfl

