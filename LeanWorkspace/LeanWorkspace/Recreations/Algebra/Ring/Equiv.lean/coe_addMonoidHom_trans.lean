import Mathlib

variable {F α β R S S' : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S] (f : R ≃+* S) (x : R)

theorem coe_addMonoidHom_trans [NonUnitalNonAssocSemiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R →+ S') = (e₂ : S →+ S').comp ↑e₁ := rfl

