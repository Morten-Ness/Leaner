import Mathlib

variable {R S M N : Type*}

variable (S) [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]

variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]

variable (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f]

variable (M' M'' : Submodule R M)

theorem localized₀_inf :
    (M' ⊓ M'').localized₀ p f = M'.localized₀ p f ⊓ M''.localized₀ p f := by
  simp only [Submodule.ext_iff, Submodule.mem_inf, Submodule.mem_localized₀]
  refine fun x ↦ ⟨by grind, ?_⟩
  rintro ⟨⟨i, hi, s, hs⟩, j, hj, t, ht⟩
  have h := ht.trans hs.symm
  rw [IsLocalizedModule.mk'_eq_mk'_iff] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨(k * t) • i, ⟨M'.smul_of_tower_mem (k * t) hi, ?_⟩, k * s * t, ?_⟩
  · rw [mul_smul, hk, smul_smul]
    exact M''.smul_of_tower_mem (k * s) hj
  · rwa [mul_smul, hk, smul_smul, IsLocalizedModule.mk'_cancel_left]

