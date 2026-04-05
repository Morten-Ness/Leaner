import Mathlib

open scoped Ring

variable {R : Type u}

theorem mem_of_star_mem {S R : Type*} [InvolutiveStar R] [SetLike S R] [StarMemClass S R]
    {s : S} {r : R} (hr : star r ∈ s) : r ∈ s := by rw [← star_star r]; exact star_mem hr

