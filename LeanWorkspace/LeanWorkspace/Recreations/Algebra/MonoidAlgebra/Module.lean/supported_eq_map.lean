import Mathlib

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S M : Type*}

variable {S : Type*}

variable [Semiring R] [Semiring S] [Module R S] {s t : Set M} {x : S[M]}

theorem supported_eq_map :
    MonoidAlgebra.supported R S s = (Finsupp.supported S R s).map (MonoidAlgebra.coeffLinearEquiv R).symm.toLinearMap := Submodule.comap_equiv_eq_map_symm ..

