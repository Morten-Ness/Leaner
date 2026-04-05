import Mathlib

variable {R S M N : Type*}

variable (S) [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]

variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]

variable (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f]

variable (M' M'' : Submodule R M)

theorem map_le_localized₀ : M'.map f ≤ Submodule.localized₀ p f M' := by
  rintro - ⟨x, hx, rfl⟩
  rw [Submodule.mem_localized₀]
  exact ⟨x, hx, 1, IsLocalizedModule.mk'_one p f x⟩

