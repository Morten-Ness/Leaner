import Mathlib

variable {R : Type*} [CommSemiring R] (S : Submonoid R)

variable {A Aₛ : Type*} [CommSemiring A] [Algebra R A]

variable [CommSemiring Aₛ] [Algebra A Aₛ] [Algebra R Aₛ] [IsScalarTower R A Aₛ]

theorem IsLocalization.mk'_eq_mk' [IsLocalization S A] (x : R) (s : S) :
    IsLocalization.mk' A x s = IsLocalizedModule.mk' (Algebra.linearMap R A) x s := by
  rw [← IsLocalizedModule.smul_inj (Algebra.linearMap R A) s, IsLocalizedModule.mk'_cancel']
  exact IsLocalization.smul_mk'_self

