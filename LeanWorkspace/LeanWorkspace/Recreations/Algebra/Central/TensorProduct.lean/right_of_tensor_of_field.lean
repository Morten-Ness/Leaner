import Mathlib

variable (K B C : Type*) [CommSemiring K] [Semiring B] [Semiring C] [Algebra K B] [Algebra K C]

theorem right_of_tensor_of_field (K B C : Type*) [Field K] [Ring B] [Ring C] [Nontrivial B]
    [Algebra K B] [Algebra K C] [Algebra.IsCentral K (B ⊗[K] C)] : Algebra.IsCentral K C := Algebra.IsCentral.right_of_tensor K B C <| FaithfulSMul.algebraMap_injective K B

