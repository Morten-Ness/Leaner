import Mathlib

variable {R : Type u} [CommRing R]

theorem tensorHom_tmul {K L M N : ModuleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) (k : K) (m : M) :
    (f ⊗ₘ g) (k ⊗ₜ m) = f k ⊗ₜ g m := rfl

