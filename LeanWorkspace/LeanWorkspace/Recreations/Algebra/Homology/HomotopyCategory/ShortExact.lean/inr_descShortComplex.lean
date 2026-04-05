import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

variable (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)

theorem inr_descShortComplex : inr S.f ≫ CochainComplex.mappingCone.descShortComplex S = S.g := by
  simp [CochainComplex.mappingCone.descShortComplex]

