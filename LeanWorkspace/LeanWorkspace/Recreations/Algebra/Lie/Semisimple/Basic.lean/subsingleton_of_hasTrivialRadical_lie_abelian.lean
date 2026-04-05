import Mathlib

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
theorem subsingleton_of_hasTrivialRadical_lie_abelian [HasTrivialRadical R L] [h : IsLieAbelian L] :
    Subsingleton L := by
  rw [isLieAbelian_iff_center_eq_top R L, center_eq_bot] at h
  exact (LieSubmodule.subsingleton_iff R L L).mp (subsingleton_of_bot_eq_top h)

