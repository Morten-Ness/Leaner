import Mathlib

variable {R : Type u} [CommRing R]

theorem hom_tensorHom {K L M N : ModuleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) :
    (f ⊗ₘ g).hom = TensorProduct.map f.hom g.hom := rfl

