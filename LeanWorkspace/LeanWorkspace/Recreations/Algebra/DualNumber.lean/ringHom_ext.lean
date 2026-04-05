import Mathlib

variable {R A B : Type*}

variable {A : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem ringHom_ext {R' : Type*} [CommSemiring R'] {f g : R[ε] →+* R'}
    (h₀ : f.comp (algebraMap R R[ε]) = g.comp (algebraMap R R[ε]))
    (hε : f ε = g ε) : f = g := by
  letI : Algebra R R' := by
    letI := f.toAlgebra
    exact Algebra.compHom _ (algebraMap R R[ε])
  let f' : R[ε] →ₐ[R] R' :=
    { toRingHom := f
      commutes' _ := rfl }
  let g' : R[ε] →ₐ[R] R' :=
    { toRingHom := g
      commutes' r := (DFunLike.congr_fun h₀ r).symm }
  exact congr_arg AlgHom.toRingHom (show f' = g' from DualNumber.algHom_ext hε)

