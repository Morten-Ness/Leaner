import Mathlib

section

variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
theorem ihom_ev_app (M N : ModuleCat.{u} R) :
    (ihom.ev M).app N = ModuleCat.ofHom (TensorProduct.uncurry (.id R) M ((ihom M).obj N) N
      (LinearMap.lcomp _ _ homLinearEquiv.toLinearMap ∘ₗ LinearMap.id.flip)) := by
  rw [← MonoidalClosed.uncurry_id_eq_ev]
  ext : 1
  apply TensorProduct.ext'
  apply ModuleCat.monoidalClosed_uncurry

end
