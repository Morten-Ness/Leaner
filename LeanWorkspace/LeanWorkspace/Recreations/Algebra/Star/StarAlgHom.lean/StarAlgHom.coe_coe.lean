import Mathlib

variable {F R A B C D : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Star A] [Semiring B]
  [Algebra R B] [Star B] [Semiring C] [Algebra R C] [Star C] [Semiring D] [Algebra R D] [Star D]

theorem coe_coe {F : Type*} [FunLike F A B] [AlgHomClass F R A B]
    [StarHomClass F A B] (f : F) :
    ⇑(f : A →⋆ₐ[R] B) = f := rfl

initialize_simps_projections StarAlgHom (toFun → apply)

