import Mathlib

variable {R S : CommRingCat.{u}}

variable [Algebra R S]

set_option backward.isDefEq.respectTransparency false in
theorem pushout_inl_tensorProdObjIsoPushoutObj_inv_right (A : Under R) :
    pushout.inl A.hom (ofHom <| algebraMap R S) ≫ (CommRingCat.tensorProdObjIsoPushoutObj S A).inv.right =
      (ofHom <| Algebra.TensorProduct.includeRight.toRingHom) := by
  simp [CommRingCat.tensorProdObjIsoPushoutObj]

