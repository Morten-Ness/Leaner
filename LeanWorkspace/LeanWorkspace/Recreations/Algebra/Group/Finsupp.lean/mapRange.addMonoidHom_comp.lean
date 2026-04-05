import Mathlib

variable {ι F M N O G H : Type*}

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid O]

theorem mapRange.addMonoidHom_comp (f : N →+ O) (g : M →+ N) :
    Finsupp.mapRange.addMonoidHom (ι := ι) (f.comp g) =
      (Finsupp.mapRange.addMonoidHom f).comp (Finsupp.mapRange.addMonoidHom g) := by ext; simp

