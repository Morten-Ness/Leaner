import Mathlib

variable {ι : Sort uι} {R M N P : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]

variable [Module R M] [Module R N] [Module R P]

theorem map₂_sup_left (f : M →ₗ[R] N →ₗ[R] P) (p₁ p₂ : Submodule R M) (q : Submodule R N) :
    Submodule.map₂ f (p₁ ⊔ p₂) q = Submodule.map₂ f p₁ q ⊔ Submodule.map₂ f p₂ q := le_antisymm
    (Submodule.map₂_le.2 fun _mn hmn _p hp =>
      let ⟨_m, hm, _n, hn, hmn⟩ := mem_sup.1 hmn
      mem_sup.2
        ⟨_, Submodule.apply_mem_map₂ _ hm hp, _, Submodule.apply_mem_map₂ _ hn hp,
          hmn ▸ (LinearMap.map_add₂ _ _ _ _).symm⟩)
    (sup_le (Submodule.map₂_le_map₂_left le_sup_left) (Submodule.map₂_le_map₂_left le_sup_right))

