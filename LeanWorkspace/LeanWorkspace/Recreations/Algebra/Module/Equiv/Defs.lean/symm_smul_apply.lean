import Mathlib

variable {R R₁ R₂ R₃ R₄ S M M₁ M₂ M₃ M₄ N₁ N₂ : Type*}

variable {S R V W G : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid V] [Module R V] [Module S V]
  [AddCommMonoid W] [Module R W] [Module S W]
  [AddCommMonoid G] [Module R G] [Module S G]
  [SMulCommClass R S W] [SMul S R] [IsScalarTower S R V] [IsScalarTower S R W]

theorem symm_smul_apply (e : V ≃ₗ[R] W) (α : Sˣ) (x : W) :
    (α • e).symm x = (↑α⁻¹ : S) • e.symm x := rfl

