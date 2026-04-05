import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [HasZeroMorphisms C] [HasZeroMorphisms D]
  (S : ShortComplex C) {S₁ S₂ : ShortComplex C}

theorem ShortExact.map_of_exact (hS : S.ShortExact)
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] : (S.map F).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  exact hS.map F

