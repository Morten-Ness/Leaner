FAIL
import Mathlib

variable {ι : Sort _}

variable {R : Type _} [CommSemiring R]

variable {A : Type _} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

variable [FaithfulSMul R A]

theorem mker_spanSingleton :
    MonoidHom.mker (Submodule.spanSingleton R) = (IsUnit.submonoid R).map (algebraMap R A) := by
  ext r
  rw [MonoidHom.mem_mker]
  constructor
  · intro hr
    rw [Submodule.spanSingleton_apply] at hr
    exact ⟨r, IsUnit.unit_spec, hr⟩
  · rintro ⟨u, hu, rfl⟩
    rcases hu with ⟨v, rfl⟩
    rw [Submodule.spanSingleton_apply]
    exact v.isUnit.unit_spec.symm
