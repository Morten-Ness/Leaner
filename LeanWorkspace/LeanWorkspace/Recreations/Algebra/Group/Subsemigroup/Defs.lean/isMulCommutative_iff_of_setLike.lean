import Mathlib

variable {M : Type*} {N : Type*}

theorem isMulCommutative_iff_of_setLike {S M : Type*} [SetLike S M] [Mul M] [MulMemClass S M]
    {s : S} : IsMulCommutative s ↔ ∀ a ∈ s, ∀ b ∈ s, a * b = b * a := by
  simp [isMulCommutative_iff]

