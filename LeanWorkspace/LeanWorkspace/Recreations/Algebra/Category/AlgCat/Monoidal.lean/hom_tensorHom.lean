import Mathlib

open scoped MonoidalCategory

variable {R : Type u} [CommRing R]

theorem hom_tensorHom {K L M N : AlgCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) :
    (f ⊗ₘ g).hom = Algebra.TensorProduct.map f.hom g.hom := rfl

