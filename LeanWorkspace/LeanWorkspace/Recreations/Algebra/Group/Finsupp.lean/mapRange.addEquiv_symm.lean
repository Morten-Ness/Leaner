import Mathlib

variable {ι F M N O G H : Type*}

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid O]

theorem mapRange.addEquiv_symm (e : M ≃+ N) :
    (Finsupp.mapRange.addEquiv (ι := ι) e).symm = Finsupp.mapRange.addEquiv e.symm := rfl

