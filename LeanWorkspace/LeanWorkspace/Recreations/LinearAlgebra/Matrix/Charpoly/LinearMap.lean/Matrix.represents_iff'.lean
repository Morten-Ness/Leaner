import Mathlib

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

variable {R} [DecidableEq ι]

theorem Matrix.represents_iff' {A : Matrix ι ι R} {f : Module.End R M} :
    A.Represents b f ↔ ∀ j, ∑ i : ι, A i j • b i = f (b j) := by
  constructor
  · intro h i
    have := LinearMap.congr_fun h (Pi.single i 1)
    rwa [PiToModule.fromEnd_apply_single_one, PiToModule.fromMatrix_apply_single_one] at this
  · intro h
    ext
    simp_rw [LinearMap.comp_apply, LinearMap.coe_single, PiToModule.fromEnd_apply_single_one,
      PiToModule.fromMatrix_apply_single_one]
    apply h

