import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem evalCoeff_eq_zero {x : M} {c : FiniteArchimedeanClass M}
    (h : ¬∃ y : f.val.domain, y.val - x ∈ ball K c) :
    f.evalCoeff x c = 0 := by
  rw [HahnEmbedding.Partial.evalCoeff, dif_neg h]

