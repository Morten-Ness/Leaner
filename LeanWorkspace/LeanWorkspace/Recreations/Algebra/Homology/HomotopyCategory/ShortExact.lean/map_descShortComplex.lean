import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

variable (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)

variable (S₁ S₂ : ShortComplex (CochainComplex C ℤ)) (f : S₁ ⟶ S₂)

theorem map_descShortComplex : map S₁.f S₂.f f.τ₁ f.τ₂ f.comm₁₂.symm ≫ CochainComplex.mappingCone.descShortComplex S₂ =
    CochainComplex.mappingCone.descShortComplex S₁ ≫ f.τ₃ := by
  ext i
  simpa [CochainComplex.mappingCone.ext_from_iff _ _ _ rfl, map] using
    congr_fun (congr_arg HomologicalComplex.Hom.f f.comm₂₃) i

