import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

variable (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)

theorem inr_f_descShortComplex_f (n : ℤ) : (inr S.f).f n ≫ (CochainComplex.mappingCone.descShortComplex S).f n = S.g.f n := by
  simp [CochainComplex.mappingCone.descShortComplex]

