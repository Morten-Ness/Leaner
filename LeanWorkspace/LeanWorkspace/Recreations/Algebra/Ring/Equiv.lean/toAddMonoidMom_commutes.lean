import Mathlib

variable {F α β R S S' : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring S']

theorem toAddMonoidMom_commutes (f : R ≃+* S) :
    (f : R →+* S).toAddMonoidHom = (f : R ≃+ S).toAddMonoidHom := rfl

