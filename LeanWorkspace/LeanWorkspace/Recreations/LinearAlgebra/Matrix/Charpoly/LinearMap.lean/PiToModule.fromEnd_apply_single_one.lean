import Mathlib

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

theorem PiToModule.fromEnd_apply_single_one [DecidableEq ι] (f : Module.End R M) (i : ι) :
    PiToModule.fromEnd R b f (Pi.single i 1) = f (b i) := by
  rw [PiToModule.fromEnd_apply, Fintype.linearCombination_apply_single, one_smul]

