import Mathlib

variable {X G : Type*} {A B C : Set X}

variable [Group G] [MulAction G X]

theorem restr_refl_symm (A : Set X) :
    ((Equidecomp.refl X G).restr A).symm = (Equidecomp.refl X G).restr A := rfl

