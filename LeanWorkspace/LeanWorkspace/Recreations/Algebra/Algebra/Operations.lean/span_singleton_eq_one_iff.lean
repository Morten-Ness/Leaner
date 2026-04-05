import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

variable [FaithfulSMul R A]

theorem span_singleton_eq_one_iff {x : A} : span R {x} = 1 ↔ ∃ r : Rˣ, x = algebraMap R A r where
  mp h := by
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp (h ▸ mem_span_singleton_self x)
    have ⟨r', eq⟩ := mem_span_singleton.mp (h ▸ Submodule.algebraMap_mem 1)
    rw [Algebra.smul_def, ← Submodule.map_mul, (FaithfulSMul.algebraMap_injective R A).eq_iff] at eq
    exact ⟨.mkOfMulEqOne _ _ (mul_comm _ r ▸ eq), rfl⟩
  mpr := by rintro ⟨r, rfl⟩; exact Submodule.span_singleton_algebraMap_of_isUnit r.isUnit

