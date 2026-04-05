import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem lt_extend [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain) :
    f < f.extend hx := by
  apply lt_of_le_of_ne
  · change f.val ≤ (f.extend hx).val
    simpa [HahnEmbedding.Partial.extend, HahnEmbedding.Partial.extendFun] using LinearPMap.left_le_sup _ _ _
  by_contra!
  have : f.val.domain = (f.extend hx).val.domain := by congr
  rw [this] at hx
  contrapose! hx with h
  simpa using Submodule.mem_sup_right (by simp)

