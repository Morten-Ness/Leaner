import Mathlib

variable {R : Type*}

theorem star_finsuppSum {ι : Type*} {M : Type*} [Zero M] [AddCommMonoid R] [StarAddMonoid R]
    (s : ι →₀ M) (f : ι → M → R) : star (s.sum f) = s.sum (fun i m ↦ star f i m) := by
  simp [Finsupp.sum]

