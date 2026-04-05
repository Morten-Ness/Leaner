import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [HasZeroMorphisms C] [HasZeroMorphisms D]
  (S : ShortComplex C) {S₁ S₂ : ShortComplex C}

theorem ShortExact.map (h : S.ShortExact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] [Mono (F.map S.f)] [Epi (F.map S.g)] :
    (S.map F).ShortExact where
  exact := h.exact.map F
  mono_f := (inferInstance : Mono (F.map S.f))
  epi_g := (inferInstance : Epi (F.map S.g))

