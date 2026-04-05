import Mathlib

variable {α : Type u} {β : Type v}

variable [CommMonoid α]

theorem mk_bijective : Function.Bijective (@ConjClasses.mk α _) := ⟨ConjClasses.mk_injective, ConjClasses.mk_surjective⟩

