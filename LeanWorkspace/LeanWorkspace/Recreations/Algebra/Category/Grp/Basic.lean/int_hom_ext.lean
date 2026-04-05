import Mathlib

theorem int_hom_ext {G : AddCommGrpCat.{0}} (f g : AddCommGrpCat.of ℤ ⟶ G)
    (w : f (1 : ℤ) = g (1 : ℤ)) : f = g := GrpCat.hom_ext (AddMonoidHom.ext_int w)

-- TODO: this argument should be generalised to the situation where
-- the forgetful functor is representable.

