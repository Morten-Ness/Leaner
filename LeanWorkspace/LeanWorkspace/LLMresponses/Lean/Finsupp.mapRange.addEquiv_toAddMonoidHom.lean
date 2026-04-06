FAIL
import Mathlib

variable {ι F M N O G H : Type*}

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid O]

theorem mapRange.addEquiv_toAddMonoidHom (e : M ≃+ N) :
    (Finsupp.mapRange.addEquiv (ι := ι) e).toAddMonoidHom =
      Finsupp.mapRange.addMonoidHom (ι := ι) e.toAddMonoidHom e.map_zero := by
  rfl
