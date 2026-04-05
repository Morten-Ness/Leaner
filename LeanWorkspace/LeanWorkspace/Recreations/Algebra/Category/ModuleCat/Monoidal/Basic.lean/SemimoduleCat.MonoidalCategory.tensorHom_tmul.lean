import Mathlib

variable {R : Type u} [CommSemiring R]

theorem tensorHom_tmul {K L M N : SemimoduleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) (k : K) (m : M) :
    (f ⊗ₘ g) (k ⊗ₜ m) = f k ⊗ₜ g m := rfl

