import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable (s : Subsemiring R)

theorem map_le_iff_le_comap {f : R →+* S} {s : Subsemiring R} {t : Subsemiring S} :
    s.map f ≤ t ↔ s ≤ t.comap f := Set.image_subset_iff

