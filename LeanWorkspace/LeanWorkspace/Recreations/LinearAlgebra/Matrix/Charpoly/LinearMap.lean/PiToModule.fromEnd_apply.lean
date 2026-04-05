import Mathlib

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

theorem PiToModule.fromEnd_apply (f : Module.End R M) (w : ι → R) :
    PiToModule.fromEnd R b f w = f (Fintype.linearCombination R b w) := rfl

