import Mathlib

variable {F α M N G : Type*}

theorem MulEquiv.inv_symm (G : Type*) [DivisionCommMonoid G] :
    (MulEquiv.inv G).symm = MulEquiv.inv G := rfl

