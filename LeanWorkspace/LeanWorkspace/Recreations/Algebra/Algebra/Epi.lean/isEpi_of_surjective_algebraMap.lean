import Mathlib

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

theorem isEpi_of_surjective_algebraMap (h : Function.Surjective (algebraMap R A)) :
    Algebra.IsEpi R A := by
  refine (Algebra.isEpi_iff_forall_one_tmul_eq R A).mpr fun a ↦ ?_
  obtain ⟨r, rfl⟩ := h a
  rw [algebraMap_eq_smul_one, smul_tmul]

