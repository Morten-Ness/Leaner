import Mathlib

variable (R : Type u) [Semiring R]

theorem hom_comp {M N O : SemimoduleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

