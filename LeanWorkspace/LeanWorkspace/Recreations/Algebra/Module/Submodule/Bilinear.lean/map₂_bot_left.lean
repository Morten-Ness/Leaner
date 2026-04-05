import Mathlib

variable {ι : Sort uι} {R M N P : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]

variable [Module R M] [Module R N] [Module R P]

theorem map₂_bot_left (f : M →ₗ[R] N →ₗ[R] P) (q : Submodule R N) : Submodule.map₂ f ⊥ q = ⊥ := eq_bot_iff.2 <|
    Submodule.map₂_le.2 fun m hm n _ => by
      rw [Submodule.mem_bot] at hm ⊢
      rw [hm, LinearMap.map_zero₂]

