import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_mem_iff {S : Type*} [SetLike S R] [InvolutiveStar R] [StarMemClass S R]
    {s : S} {x : R} : star x ∈ s ↔ x ∈ s := ⟨fun h => star_star x ▸ star_mem h, fun h => star_mem h⟩

