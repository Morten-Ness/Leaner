import Mathlib

variable {ι F M N O G H : Type*}

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid O]

theorem mapRange.addEquiv_toEquiv (e : M ≃+ N) :
    Finsupp.mapRange.addEquiv (ι := ι) e = mapRange.equiv (ι := ι) (e : M ≃ N) e.map_zero := rfl

