import Mathlib

variable (R : Type uR) [CommRing R]

variable (A : Type uA) [AddCommGroup A]

variable (A' : Type*) [AddCommGroup A']

variable (B : Type uB) [AddCommGroup B]

variable [Module R A] [Module R A'] [Module R B]

theorem dual_injective_of_surjective (f : A →ₗ[R] B) (hf : Function.Surjective f) :
    Function.Injective (dual f) := by
  intro φ ψ eq
  ext x
  obtain ⟨y, rfl⟩ := hf x
  change (dual f) φ _ = (dual f) ψ _
  rw [eq]

