import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable {R} {N : ι → Type*}

variable [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

variable (f : Π i, M i →ₗ[R] N i)

theorem lmap_surjective : Function.Surjective (DirectSum.lmap f) ↔ (∀ i, Function.Surjective (f i)) := by
  classical exact DFinsupp.mapRange_surjective (hf := fun _ ↦ map_zero _)

