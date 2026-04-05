import Mathlib

variable {R : Type u} [CommSemiring R]

theorem tensorμ_eq_tensorTensorTensorComm {A B C D : SemimoduleCat R} :
    tensorμ A B C D = ofHom (TensorProduct.tensorTensorTensorComm R A B C D).toLinearMap := SemimoduleCat.hom_ext <| TensorProduct.ext <| TensorProduct.ext <| LinearMap.ext₂ fun _ _ =>
    TensorProduct.ext <| LinearMap.ext₂ fun _ _ => rfl

