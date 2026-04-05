import Mathlib

variable {R : Type*} [CommSemiring R]

variable {l m n : Type*} [Fintype n] [DecidableEq n]

variable {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]

variable (v₁ : Basis n R M₁) (v₂ : Basis m R M₂)

theorem Matrix.toLin_apply_eq_zero_iff {R M₁ M₂ : Type*} [Finite m] [CommRing R]
    [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁] [Module R M₂]
    {v₁ : Module.Basis n R M₁} {v₂ : Module.Basis m R M₂} {A : Matrix m n R} {x : M₁} :
    A.toLin v₁ v₂ x = 0 ↔ ∀ j, (A *ᵥ v₁.repr x) j = 0 := by
  have := Fintype.ofFinite m
  rw [toLin_apply]
  exact ⟨Fintype.linearIndependent_iff.mp v₂.linearIndependent _, fun h ↦ by simp [h]⟩

