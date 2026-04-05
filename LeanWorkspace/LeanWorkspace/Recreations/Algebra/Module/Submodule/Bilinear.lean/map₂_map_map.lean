import Mathlib

variable {ι : Sort uι} {R M N P : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]

variable [Module R M] [Module R N] [Module R P]

variable {M₂ N₂ P₂ : Type*}

variable [AddCommMonoid M₂] [AddCommMonoid N₂] [AddCommMonoid P₂]

variable [Module R M₂] [Module R N₂] [Module R P₂]

theorem map₂_map_map
    (f : M₂ →ₗ[R] N₂ →ₗ[R] P) (g : M →ₗ[R] M₂) (h : N →ₗ[R] N₂)
    (p : Submodule R M) (q : Submodule R N) :
    Submodule.map₂ f (map g p) (map h q) = Submodule.map₂ (f.compl₁₂ g h) p q := by
  rw [Submodule.map₂_map_right, Submodule.map₂_map_left]
  rfl

