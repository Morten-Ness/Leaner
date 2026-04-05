import Mathlib

variable (K B C : Type*) [CommSemiring K] [Semiring B] [Semiring C] [Algebra K B] [Algebra K C]

theorem right_of_tensor (inj : Function.Injective (algebraMap K B)) [Module.Flat K C]
    [Algebra.IsCentral K (B ⊗[K] C)] : Algebra.IsCentral K C := have : Algebra.IsCentral K (C ⊗[K] B) := Algebra.IsCentral.of_algEquiv K _ _ <| Algebra.TensorProduct.comm _ _ _
  Algebra.IsCentral.left_of_tensor K C B inj

