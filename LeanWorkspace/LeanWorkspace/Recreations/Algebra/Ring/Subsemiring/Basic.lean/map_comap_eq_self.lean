import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem map_comap_eq_self
    {f : R →+* S} {t : Subsemiring S} (h : t ≤ f.rangeS) : (t.comap f).map f = t := by
  simpa only [inf_of_le_left h] using Subsemiring.map_comap_eq f t

