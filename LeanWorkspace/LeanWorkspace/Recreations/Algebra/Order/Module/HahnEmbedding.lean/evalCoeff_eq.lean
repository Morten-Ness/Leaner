import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem evalCoeff_eq [IsOrderedAddMonoid R] [Archimedean R] {x : M} {c : FiniteArchimedeanClass M}
    {y : f.val.domain} (hy : y.val - x ∈ ball K c) :
    HahnEmbedding.Partial.evalCoeff f x c = (ofLex (f.val y)).coeff c := by
  have hnonempty : ∃ y : f.val.domain, y.val - x ∈ ball K c := ⟨y, hy⟩
  simpa [HahnEmbedding.Partial.evalCoeff, dif_pos hnonempty] using HahnEmbedding.Partial.coeff_eq_of_mem f x hnonempty.choose_spec hy le_rfl

