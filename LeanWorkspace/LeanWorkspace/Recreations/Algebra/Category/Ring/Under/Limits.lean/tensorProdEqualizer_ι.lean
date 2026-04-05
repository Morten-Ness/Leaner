import Mathlib

variable {R S : CommRingCat.{u}}

variable [Algebra R S]

theorem tensorProdEqualizer_ι {A B : CommRingCat.Under R} (f g : A ⟶ B) :
    (CommRingCat.Under.tensorProdEqualizer f g).ι = (tensorProd R S).map
      ((AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder) := rfl

