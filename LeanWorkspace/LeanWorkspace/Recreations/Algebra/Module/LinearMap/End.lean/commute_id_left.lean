import Mathlib

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (f : Module.End R M)

theorem commute_id_left : Commute LinearMap.id f := by ext; simp

