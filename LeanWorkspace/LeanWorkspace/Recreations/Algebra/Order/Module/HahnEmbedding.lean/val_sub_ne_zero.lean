import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem val_sub_ne_zero {x : M} (hx : x ∉ f.val.domain) (y : f.val.domain) : y.val - x ≠ 0 := by
  contrapose! hx
  obtain rfl : x = y.val := (sub_eq_zero.mp hx).symm
  simp

