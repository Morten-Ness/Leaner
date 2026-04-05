import Mathlib

variable {ι : Sort uι} {R M N P : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]

variable [Module R M] [Module R N] [Module R P]

theorem map₂_le_map₂ {f : M →ₗ[R] N →ₗ[R] P} {p₁ p₂ : Submodule R M} {q₁ q₂ : Submodule R N}
    (hp : p₁ ≤ p₂) (hq : q₁ ≤ q₂) : Submodule.map₂ f p₁ q₁ ≤ Submodule.map₂ f p₂ q₂ := Submodule.map₂_le.2 fun _m hm _n hn => Submodule.apply_mem_map₂ _ (hp hm) (hq hn)

