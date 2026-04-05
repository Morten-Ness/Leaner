import Mathlib

variable {ι : Sort uι} {R M N P : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]

variable [Module R M] [Module R N] [Module R P]

theorem map₂_bot_right (f : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) : Submodule.map₂ f p ⊥ = ⊥ := eq_bot_iff.2 <|
    Submodule.map₂_le.2 fun m _hm n hn => by
      rw [Submodule.mem_bot] at hn
      rw [hn, map_zero]; simp only [mem_bot]

