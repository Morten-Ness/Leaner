import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem orderTop_eq_finiteArchimedeanClassMk [IsOrderedAddMonoid R] [Archimedean R]
    {x : f.val.domain} (hx0 : x.val ≠ 0) :
    (ofLex (f.val x)).orderTop = FiniteArchimedeanClass.mk x.val hx0 := by
  apply_fun FiniteArchimedeanClass.withTopOrderIso M
  simp [HahnEmbedding.Partial.orderTop_eq_archimedeanClassMk]

