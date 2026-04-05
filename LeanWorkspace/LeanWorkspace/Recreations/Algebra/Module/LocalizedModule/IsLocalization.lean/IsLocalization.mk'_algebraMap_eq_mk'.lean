import Mathlib

variable {R : Type*} [CommSemiring R] (S : Submonoid R)

variable {A Aₛ : Type*} [CommSemiring A] [Algebra R A]

variable [CommSemiring Aₛ] [Algebra A Aₛ] [Algebra R Aₛ] [IsScalarTower R A Aₛ]

theorem IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ]
    {x : A} {s : S} : IsLocalization.mk' Aₛ x ⟨_, Algebra.mem_algebraMapSubmonoid_of_mem s⟩ =
      IsLocalizedModule.mk' (IsScalarTower.toAlgHom R A Aₛ).toLinearMap x s := by
  rw [← IsLocalizedModule.smul_inj (IsScalarTower.toAlgHom R A Aₛ).toLinearMap s,
    IsLocalizedModule.mk'_cancel', Submonoid.smul_def, ← algebraMap_smul A]
  exact IsLocalization.smul_mk'_self (m := ⟨_, _⟩)

