import Mathlib

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {p p' : Submodule R M}

theorem inclusion_injective (h : p ≤ p') : Function.Injective (Submodule.inclusion h) := fun _ _ h =>
  Subtype.val_injective (Subtype.mk.inj h)

