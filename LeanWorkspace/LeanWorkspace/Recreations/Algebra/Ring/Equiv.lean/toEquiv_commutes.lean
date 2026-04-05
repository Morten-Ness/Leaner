import Mathlib

variable {F α β R S S' : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring S']

theorem toEquiv_commutes (f : R ≃+* S) : (f : R ≃+ S).toEquiv = (f : R ≃* S).toEquiv := rfl

