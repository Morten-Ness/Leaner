import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem coeff_ne_zero [IsOrderedAddMonoid R] [Archimedean R] {x : f.val.domain} (hx0 : x.val ≠ 0) :
    (ofLex (f.val x)).coeff (FiniteArchimedeanClass.mk x.val hx0) ≠ 0 := HahnSeries.coeff_orderTop_ne <| HahnEmbedding.Partial.orderTop_eq_finiteArchimedeanClassMk f hx0

