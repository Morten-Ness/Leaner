import Mathlib

variable {R A : Type*}

variable [Ring R] [StarRing R]

theorem isStarNormal_of_mem {x : R} (hx : x ∈ skewAdjoint R) : IsStarNormal x := ⟨by
    simp only [skewAdjoint.mem_iff] at hx
    simp only [hx, Commute.neg_left, Commute.refl]⟩

