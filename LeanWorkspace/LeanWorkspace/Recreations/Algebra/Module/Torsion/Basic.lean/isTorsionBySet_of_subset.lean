import Mathlib

variable {R M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem isTorsionBySet_of_subset {s t : Set R} (h : s ⊆ t)
    (ht : IsTorsionBySet R M t) : IsTorsionBySet R M s := fun m r ↦ @ht m ⟨r, h r.2⟩

