import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid α] [LE α] [MulLeftMono α] {s : Finset ι} {f : ι → α}

theorem mulLECancellable_prod :
    MulLECancellable (∏ i ∈ s, f i) ↔ ∀ ⦃i⦄, i ∈ s → MulLECancellable (f i) := by
  induction s using Finset.cons_induction <;> simp [*]

