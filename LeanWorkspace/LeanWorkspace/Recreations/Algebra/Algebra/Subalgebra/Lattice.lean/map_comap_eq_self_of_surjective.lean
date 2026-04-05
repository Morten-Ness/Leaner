import Mathlib

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem map_comap_eq_self_of_surjective
    {f : A →ₐ[R] B} (hf : Function.Surjective f) (S : Subalgebra R B) : (S.comap f).map f = S := Subalgebra.map_comap_eq_self <| by simp [(AlgHom.range_eq_top f).2 hf]

