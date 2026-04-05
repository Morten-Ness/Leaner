import Mathlib

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem degree_eq_of_mem_mem {x : M} {i j : ι} (hxi : x ∈ ℳ i) (hxj : x ∈ ℳ j) (hx : x ≠ 0) :
    i = j := by
  contrapose! hx; rw [← DirectSum.decompose_of_mem_same ℳ hxj, DirectSum.decompose_of_mem_ne ℳ hxi hx]

