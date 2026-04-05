import Mathlib

open scoped DirectSum

variable {ι : Type uι}

variable (R : Type uR) (A : ι → Type uA) {B : Type uB}

variable [CommSemiring R] [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]

variable [AddMonoid ι] [GSemiring A]

variable [Semiring B] [GAlgebra R A] [Algebra R B]

variable [DecidableEq ι]

theorem algHom_ext ⦃f g : (⨁ i, A i) →ₐ[R] B⦄ (h : ∀ i x, f (of A i x) = g (of A i x)) : f = g := DirectSum.algHom_ext' R A fun i => LinearMap.ext <| h i

