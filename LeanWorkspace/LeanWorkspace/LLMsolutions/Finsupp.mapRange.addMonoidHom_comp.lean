FAIL
import Mathlib

variable {ι F M N O G H : Type*}

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid O]

theorem mapRange.addMonoidHom_comp (f : N →+ O) (g : M →+ N) :
    Finsupp.mapRange.addMonoidHom (ι := ι) f (f.map_zero) ∘
      Finsupp.mapRange.addMonoidHom (ι := ι) g (g.map_zero) =
    Finsupp.mapRange.addMonoidHom (ι := ι) (f.comp g) ((f.comp g).map_zero) := by
  ext x i
  simp [AddMonoidHom.comp_apply]
