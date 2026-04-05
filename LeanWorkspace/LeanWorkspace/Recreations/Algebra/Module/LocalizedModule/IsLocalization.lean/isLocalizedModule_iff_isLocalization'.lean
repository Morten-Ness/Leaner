import Mathlib

variable {R : Type*} [CommSemiring R] (S : Submonoid R)

variable {A Aₛ : Type*} [CommSemiring A] [Algebra R A]

variable [CommSemiring Aₛ] [Algebra A Aₛ] [Algebra R Aₛ] [IsScalarTower R A Aₛ]

theorem isLocalizedModule_iff_isLocalization' :
    IsLocalizedModule S (Algebra.linearMap R A) ↔ IsLocalization S A := by
  convert isLocalizedModule_iff_isLocalization (S := S) (A := R) (Aₛ := A)
  exact (Submonoid.map_id S).symm

