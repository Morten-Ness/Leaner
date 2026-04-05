import Mathlib

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

theorem PiToModule.fromMatrix_apply [DecidableEq ι] (A : Matrix ι ι R) (w : ι → R) :
    PiToModule.fromMatrix R b A w = Fintype.linearCombination R b (A *ᵥ w) := rfl

