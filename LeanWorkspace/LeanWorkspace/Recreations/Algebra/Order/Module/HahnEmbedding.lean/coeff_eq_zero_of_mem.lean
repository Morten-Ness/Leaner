import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem coeff_eq_zero_of_mem [IsOrderedAddMonoid R] [Archimedean R]
    {c : FiniteArchimedeanClass M} {x : f.val.domain} (hx : x.val ∈ ball K c)
    {d : FiniteArchimedeanClass M} (hd : d.val ≤ c) : (ofLex (f.val x)).coeff d = 0 := by
  obtain rfl | ne := eq_or_ne x 0
  · simp
  apply HahnSeries.coeff_eq_zero_of_lt_orderTop
  apply_fun FiniteArchimedeanClass.withTopOrderIso _
  rw [HahnEmbedding.Partial.orderTop_eq_archimedeanClassMk, FiniteArchimedeanClass.withTopOrderIso_apply_coe]
  apply lt_of_le_of_lt hd
  simpa using hx (by simpa using ne)

