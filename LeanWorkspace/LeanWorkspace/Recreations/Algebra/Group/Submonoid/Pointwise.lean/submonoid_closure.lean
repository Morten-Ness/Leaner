import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α] {s : Set α}

theorem submonoid_closure (hpos : ∀ x : α, x ∈ s → 1 ≤ x) (h : s.IsPWO) :
    Set.IsPWO (Submonoid.closure s : Set α) := by
  rw [Submonoid.closure_eq_image_prod]
  refine (h.partiallyWellOrderedOn_sublistForall₂ (· ≤ ·)).image_of_monotone_on ?_
  exact fun l1 _ l2 hl2 h12 => h12.prod_le_prod' fun x hx => hpos x <| hl2 x hx

