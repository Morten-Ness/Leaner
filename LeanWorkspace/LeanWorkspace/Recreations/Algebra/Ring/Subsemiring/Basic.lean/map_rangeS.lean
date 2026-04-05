import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable (g : S →+* T) (f : R →+* S)

theorem map_rangeS : f.rangeS.map g = (g.comp f).rangeS := by
  simpa only [RingHom.rangeS_eq_map] using Subsemiring.map_map (⊤ : Subsemiring R) g f

