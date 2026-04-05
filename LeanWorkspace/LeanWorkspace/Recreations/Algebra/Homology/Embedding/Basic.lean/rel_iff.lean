import Mathlib

variable {ι ι' : Type*} (c : ComplexShape ι) (c' : ComplexShape ι')

variable (e : Embedding c c')

theorem rel_iff [e.IsRelIff] (i₁ i₂ : ι) : c'.Rel (e.f i₁) (e.f i₂) ↔ c.Rel i₁ i₂ := by
  constructor
  · apply IsRelIff.rel'
  · exact e.rel

