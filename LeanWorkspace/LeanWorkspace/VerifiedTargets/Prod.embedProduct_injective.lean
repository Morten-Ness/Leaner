import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

theorem embedProduct_injective (α : Type*) [Monoid α] : Function.Injective (Units.embedProduct α) := fun _ _ h => Units.ext <| (congr_arg Prod.fst h :)

