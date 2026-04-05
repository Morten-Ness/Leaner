import Mathlib

variable {R R₁ R₂ R₃ R₄ S M M₁ M₂ M₃ M₄ N₁ N₂ : Type*}

variable {S R V W G : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid V] [Module R V] [Module S V]
  [AddCommMonoid W] [Module R W] [Module S W]
  [AddCommMonoid G] [Module R G] [Module S G]
  [SMulCommClass R S W] [SMul S R] [IsScalarTower S R V] [IsScalarTower S R W]

theorem trans_smul [IsScalarTower S R G]
    (α : Sˣ) (e : G ≃ₗ[R] V) (f : V ≃ₗ[R] W) :
    e.trans (α • f) = α • (e.trans f) := by ext; simp

