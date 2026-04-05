import Mathlib

variable {R : Type*} [CommSemiring R] (S : Submonoid R)

variable {A Aₛ : Type*} [CommSemiring A] [Algebra R A]

variable [CommSemiring Aₛ] [Algebra A Aₛ] [Algebra R Aₛ] [IsScalarTower R A Aₛ]

theorem isLocalizedModule_iff_isLocalization :
    IsLocalizedModule S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap ↔
      IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ := by
  rw [isLocalizedModule_iff, isLocalization_iff]
  refine and_congr ?_ (and_congr (forall_congr' fun _ ↦ ?_) (forall₂_congr fun _ _ ↦ ?_))
  · simp_rw [← (Algebra.lmul R Aₛ).commutes, Algebra.lmul_isUnit_iff, Subtype.forall,
      Algebra.algebraMapSubmonoid, ← SetLike.mem_coe, Submonoid.coe_map,
      Set.forall_mem_image, ← IsScalarTower.algebraMap_apply]
  · simp_rw [Prod.exists, Subtype.exists, Algebra.algebraMapSubmonoid]
    simp [← IsScalarTower.algebraMap_apply, Submonoid.mk_smul, Algebra.smul_def, mul_comm]
  · congr!; simp_rw [Subtype.exists, Algebra.algebraMapSubmonoid]; simp [Algebra.smul_def]

