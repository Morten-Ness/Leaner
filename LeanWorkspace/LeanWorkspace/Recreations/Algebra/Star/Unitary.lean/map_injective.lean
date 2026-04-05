import Mathlib

variable {R : Type*}

variable {R S T : Type*} [Monoid R] [StarMul R] [Monoid S] [StarMul S] [Monoid T] [StarMul T]

theorem map_injective {f : R →⋆* S} (hf : Function.Injective f) :
    Function.Injective (Unitary.map f : unitary R → unitary S) := Subtype.map_injective (fun _ ↦ Unitary.map_mem f) hf

