import Mathlib

variable {R : Type u} [CommRing R]

theorem tensorμ_eq_tensorTensorTensorComm {A B C D : ModuleCat R} :
    tensorμ A B C D = ofHom (TensorProduct.tensorTensorTensorComm R A B C D).toLinearMap := ModuleCat.hom_ext <| TensorProduct.ext <| TensorProduct.ext <| LinearMap.ext₂ fun _ _ =>
    TensorProduct.ext <| LinearMap.ext₂ fun _ _ => rfl

