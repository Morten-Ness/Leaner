import Mathlib

variable {R M N N'} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

variable [AddCommGroup N'] [Module R N'] (S : Submonoid R) (f : N →ₗ[R] N') [IsLocalizedModule S f]

theorem Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
    [hM : Module.Finite R M] (g₁ g₂ : M →ₗ[R] N) (h : f.comp g₁ = f.comp g₂) :
    ∃ (s : S), s • g₁ = s • g₂ := by
  classical
  have : ∀ x, ∃ s : S, s • g₁ x = s • g₂ x := fun x ↦
    IsLocalizedModule.exists_of_eq (S := S) (f := f) (LinearMap.congr_fun h x)
  choose s hs using this
  obtain ⟨σ, hσ⟩ := hM
  use σ.prod s
  rw [← sub_eq_zero, ← LinearMap.ker_eq_top, ← top_le_iff, ← hσ, Submodule.span_le]
  intro x hx
  simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    sub_eq_zero, ← Finset.prod_erase_mul σ s hx, mul_smul, hs]

