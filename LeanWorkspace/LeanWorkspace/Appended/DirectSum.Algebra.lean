import Mathlib

section

open scoped DirectSum

variable {ι : Type uι}

variable (R : Type uR) (A : ι → Type uA) {B : Type uB}

variable [CommSemiring R] [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]

variable [AddMonoid ι] [GSemiring A]

variable [Semiring B] [GAlgebra R A] [Algebra R B]

variable [DecidableEq ι]

theorem algHom_ext' ⦃f g : (⨁ i, A i) →ₐ[R] B⦄
    (h : ∀ i, f.toLinearMap.comp (DirectSum.lof _ _ A i) = g.toLinearMap.comp (DirectSum.lof _ _ A i)) : f = g := AlgHom.toLinearMap_injective <| DirectSum.linearMap_ext _ h

end

section

open scoped DirectSum

variable {ι : Type uι}

variable (R : Type uR) (A : ι → Type uA) {B : Type uB}

variable [CommSemiring R] [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]

variable [AddMonoid ι] [GSemiring A]

variable [Semiring B] [GAlgebra R A] [Algebra R B]

variable [DecidableEq ι]

theorem algHom_ext ⦃f g : (⨁ i, A i) →ₐ[R] B⦄ (h : ∀ i x, f (of A i x) = g (of A i x)) : f = g := DirectSum.algHom_ext' R A fun i => LinearMap.ext <| h i

end
