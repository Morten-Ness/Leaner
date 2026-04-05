import Mathlib

variable (R : Type u) [Semiring R]

theorem hom_bijective {M N : SemimoduleCat.{v} R} :
    Function.Bijective (Hom.hom : (M ⟶ N) → (M →ₗ[R] N)) where
  left f g h := by cases f; cases g; simpa using h
  right f := ⟨⟨f⟩, rfl⟩

