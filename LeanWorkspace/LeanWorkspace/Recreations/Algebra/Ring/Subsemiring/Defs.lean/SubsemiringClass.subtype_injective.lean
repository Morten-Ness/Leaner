import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [SetLike S R] [hSR : SubsemiringClass S R] (s : S)

theorem subtype_injective :
    Function.Injective (SubsemiringClass.subtype s) := fun _ ↦ by
  simp

-- Prefer subclasses of `Semiring` over subclasses of `SubsemiringClass`.

