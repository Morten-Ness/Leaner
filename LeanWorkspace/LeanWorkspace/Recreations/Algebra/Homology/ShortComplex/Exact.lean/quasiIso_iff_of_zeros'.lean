import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Abelian C]

set_option backward.isDefEq.respectTransparency false in
theorem quasiIso_iff_of_zeros' {S₁ S₂ : CategoryTheory.ShortComplex C} (φ : S₁ ⟶ S₂)
    (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g = 0) :
    QuasiIso φ ↔
      (CategoryTheory.ShortComplex.mk S₁.f φ.τ₂ (by rw [← φ.comm₁₂, hf₂, comp_zero])).Exact ∧ Epi φ.τ₂ := by
  rw [← quasiIso_opMap_iff, CategoryTheory.ShortComplex.quasiIso_iff_of_zeros]
  rotate_left
  · dsimp
    rw [hg₂, op_zero]
  · dsimp
    rw [hf₂, op_zero]
  · dsimp
    rw [hg₁, op_zero]
  rw [← CategoryTheory.ShortComplex.exact_unop_iff]
  have : Mono φ.τ₂.op ↔ Epi φ.τ₂ :=
    ⟨fun _ => unop_epi_of_mono φ.τ₂.op, fun _ => op_mono_of_epi _⟩
  tauto

