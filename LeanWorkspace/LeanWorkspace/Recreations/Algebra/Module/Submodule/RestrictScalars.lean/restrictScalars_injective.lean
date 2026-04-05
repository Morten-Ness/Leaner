import Mathlib

variable (S : Type*) {R M : Type*} [Semiring R] [AddCommMonoid M] [Semiring S]
  [Module S M] [Module R M] [SMul S R] [IsScalarTower S R M]

theorem restrictScalars_injective :
    Function.Injective (Submodule.restrictScalars S : Submodule R M → Submodule S M) := fun _ _ h =>
  ext <| Set.ext_iff.1 (SetLike.ext'_iff.1 h :)

