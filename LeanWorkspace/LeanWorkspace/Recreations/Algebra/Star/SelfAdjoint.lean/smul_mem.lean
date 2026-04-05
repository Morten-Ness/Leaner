import Mathlib

variable {R A : Type*}

variable [Star R] [TrivialStar R] [AddCommGroup A] [StarAddMonoid A]

theorem smul_mem [Monoid R] [DistribMulAction R A] [StarModule R A] (r : R) {x : A}
    (h : x ∈ skewAdjoint A) : r • x ∈ skewAdjoint A := by
  rw [skewAdjoint.mem_iff, star_smul, star_trivial, skewAdjoint.mem_iff.mp h, smul_neg r]

