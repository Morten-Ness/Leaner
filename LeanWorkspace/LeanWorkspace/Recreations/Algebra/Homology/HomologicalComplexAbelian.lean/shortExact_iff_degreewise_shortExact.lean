import Mathlib

variable {C ι : Type*} {c : ComplexShape ι} [Category* C]

variable [Abelian C]

variable (S : ShortComplex (HomologicalComplex C c))

theorem shortExact_iff_degreewise_shortExact :
    S.ShortExact ↔ ∀ (i : ι), (S.map (eval C c i)).ShortExact := by
  constructor
  · intro hS i
    have := hS.mono_f
    have := hS.epi_g
    exact hS.map (eval C c i)
  · exact HomologicalComplex.shortExact_of_degreewise_shortExact S

