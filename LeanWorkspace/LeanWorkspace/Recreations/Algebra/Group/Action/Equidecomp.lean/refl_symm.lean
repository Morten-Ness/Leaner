import Mathlib

variable {X G : Type*} {A B C : Set X}

variable [Group G] [MulAction G X]

theorem refl_symm : (Equidecomp.refl X G).symm = Equidecomp.refl X G := rfl

