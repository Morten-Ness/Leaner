import Mathlib

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M]

variable [Module R M] [Module A M] [IsScalarTower R A M]

theorem coe_span_eq_span_of_surjective (h : Function.Surjective (algebraMap R A)) (s : Set M) :
    (Submodule.span A s : Set M) = Submodule.span R s := congr_arg ((↑) : Submodule R M → Set M) (Submodule.restrictScalars_span R A h s)

