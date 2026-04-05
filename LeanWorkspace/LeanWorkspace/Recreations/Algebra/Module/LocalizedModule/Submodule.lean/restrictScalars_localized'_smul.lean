import Mathlib

variable {R S M N : Type*}

variable (S) [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]

variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]

variable (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f]

variable (M' M'' : Submodule R M)

theorem restrictScalars_localized'_smul (I : Submodule R R) (N' : Submodule S N) :
    (I.localized' S p (Algebra.linearMap R S) • N').restrictScalars R =
      I • N'.restrictScalars R := by
  refine le_antisymm (fun x hx ↦ ?_) (Submodule.smul_le.mpr fun r hr n hn ↦ ?_)
  · refine smul_induction_on ((Submodule.restrictScalars_mem _ _ _).mp hx) ?_ fun _ _ ↦ add_mem
    rintro _ ⟨r, hr, s, rfl⟩ n hn
    rw [← IsLocalization.mk'_eq_mk', IsLocalization.mk'_eq_mul_mk'_one, mul_smul, algebraMap_smul]
    exact smul_mem_smul hr ((Submodule.restrictScalars_mem _ _ _).mpr <| smul_mem _ _ hn)
  · rw [← algebraMap_smul S, Submodule.restrictScalars_mem]
    exact Submodule.smul_mem_smul ⟨_, hr, 1, by simp⟩ hn

