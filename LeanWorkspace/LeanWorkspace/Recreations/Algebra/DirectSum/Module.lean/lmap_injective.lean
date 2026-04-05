import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable {R} {N : ι → Type*}

variable [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

variable (f : Π i, M i →ₗ[R] N i)

theorem lmap_injective : Function.Injective (DirectSum.lmap f) ↔ ∀ i, Function.Injective (f i) := by
  classical exact DFinsupp.mapRange_injective (hf := fun _ ↦ map_zero _)

