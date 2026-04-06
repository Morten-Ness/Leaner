import Mathlib

variable {R S : Type*}

theorem toIntAlgHom_injective [Ring R] [Ring S] :
    Function.Injective (RingHom.toIntAlgHom : (R →+* S) → _) := by
  intro f g h
  ext x
  exact AlgHom.congr_fun h x
