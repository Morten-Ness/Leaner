import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α] {s : Set α}

theorem submonoid_closure (hpos : ∀ x : α, x ∈ s → 1 ≤ x) (h : s.IsPWO) :
    Set.IsPWO (Submonoid.closure s : Set α) := by
  simpa [Submonoid.closure_eq] using h.submonoid_closure hpos
