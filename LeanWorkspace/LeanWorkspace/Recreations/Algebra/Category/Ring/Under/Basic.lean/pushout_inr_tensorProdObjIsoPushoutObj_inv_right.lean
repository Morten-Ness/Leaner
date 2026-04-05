import Mathlib

variable {R S : CommRingCat.{u}}

variable [Algebra R S]

set_option backward.isDefEq.respectTransparency false in
theorem pushout_inr_tensorProdObjIsoPushoutObj_inv_right (A : Under R) :
    pushout.inr A.hom (ofHom <| algebraMap R S) ≫
      (CommRingCat.tensorProdObjIsoPushoutObj S A).inv.right =
      (CommRingCat.ofHom <| Algebra.TensorProduct.includeLeftRingHom) := by
  simp [CommRingCat.tensorProdObjIsoPushoutObj]

