import Mathlib

variable {ι : Sort uι} {R M N P : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]

variable [Module R M] [Module R N] [Module R P]

theorem map₂_sup_right (f : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) (q₁ q₂ : Submodule R N) :
    Submodule.map₂ f p (q₁ ⊔ q₂) = Submodule.map₂ f p q₁ ⊔ Submodule.map₂ f p q₂ := le_antisymm
    (Submodule.map₂_le.2 fun _m hm _np hnp =>
      let ⟨_n, hn, _p, hp, hnp⟩ := mem_sup.1 hnp
      mem_sup.2 ⟨_, Submodule.apply_mem_map₂ _ hm hn, _, Submodule.apply_mem_map₂ _ hm hp, hnp ▸ (map_add _ _ _).symm⟩)
    (sup_le (Submodule.map₂_le_map₂_right le_sup_left) (Submodule.map₂_le_map₂_right le_sup_right))

