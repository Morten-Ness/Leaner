import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

variable (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)

theorem inl_v_descShortComplex_f (i j : ℤ) (h : i + (-1) = j) :
    (inl S.f).v i j h ≫ (CochainComplex.mappingCone.descShortComplex S).f j = 0 := by
  simp [CochainComplex.mappingCone.descShortComplex]

