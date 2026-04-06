import Mathlib

variable {ι F M N O G H : Type*}

variable [Zero M] [Zero N] [Zero O]

theorem mapRange.zeroHom_comp (f : ZeroHom N O) (f₂ : ZeroHom M N) :
    Finsupp.mapRange.zeroHom (ι := ι) (f.comp f₂) =
      (Finsupp.mapRange.zeroHom (ι := ι) f).comp (Finsupp.mapRange.zeroHom (ι := ι) f₂) := by
  ext g a
  rfl
