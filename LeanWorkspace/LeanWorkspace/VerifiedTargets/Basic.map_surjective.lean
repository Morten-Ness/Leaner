import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable {M S : Type*} [AddCommMonoid M] [SetLike S M] [AddSubmonoidClass S M]

variable {ι : Type*} {α : ι → Type*} {β : ι → Type*} [∀ i, AddCommMonoid (α i)]

variable [∀ i, AddCommMonoid (β i)] (f : ∀ (i : ι), α i →+ β i)

theorem map_surjective : Function.Surjective (DirectSum.map f) ↔ (∀ i, Function.Surjective (f i)) := by
  classical exact DFinsupp.mapRange_surjective (hf := fun _ ↦ map_zero _)

