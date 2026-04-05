import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

variable {S : Submonoid M}

theorem nontrivial_iff : Nontrivial (Submonoid M) ↔ Nontrivial M := not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans Submonoid.subsingleton_iff).trans
      not_nontrivial_iff_subsingleton.symm)

