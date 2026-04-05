import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable (s : Subsemiring R)

theorem gc_map_comap (f : R →+* S) : GaloisConnection (Subsemiring.map f) (Subsemiring.comap f) := fun _ _ =>
  Subsemiring.map_le_iff_le_comap

