import Mathlib

variable {R A B : Type*}

variable {A : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem lift_apply_apply (fe : {_fe : (A →ₐ[R] B) × B // _}) (a : A[ε]) :
    DualNumber.lift fe a = fe.val.1 a.fst + fe.val.1 a.snd * fe.val.2 := rfl

