import Mathlib

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

variable {R} [DecidableEq ι]

theorem Matrix.represents_iff {A : Matrix ι ι R} {f : Module.End R M} :
    A.Represents b f ↔
      ∀ x, Fintype.linearCombination R b (A *ᵥ x) = f (Fintype.linearCombination R b x) := ⟨fun e x => e.congr_fun x, fun H => LinearMap.ext fun x => H x⟩

