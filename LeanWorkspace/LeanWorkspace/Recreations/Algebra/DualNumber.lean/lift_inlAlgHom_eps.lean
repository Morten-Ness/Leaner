import Mathlib

variable {R A B : Type*}

variable {A : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem lift_inlAlgHom_eps :
    DualNumber.lift ⟨(inlAlgHom _ _ _, ε), DualNumber.eps_mul_eps, fun _ => DualNumber.commute_eps_left _⟩ = AlgHom.id R A[ε] := DualNumber.lift.apply_symm_apply <| AlgHom.id R A[ε]

