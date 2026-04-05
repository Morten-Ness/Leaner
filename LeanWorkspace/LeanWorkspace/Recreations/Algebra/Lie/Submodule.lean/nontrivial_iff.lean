import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem nontrivial_iff : Nontrivial (LieSubmodule R L M) ↔ Nontrivial M := not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans <| LieSubmodule.subsingleton_iff R L M).trans
      not_nontrivial_iff_subsingleton.symm)

