import Mathlib

open scoped Algebra

variable (R : Type u) (S : Type v) (M : Type w)

variable [CommSemiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]

variable [SMulCommClass S R M] [SMul R S] [IsScalarTower R S M]

theorem End.algebraMap_isUnit_inv_apply_eq_iff' {x : R}
    (h : IsUnit (algebraMap R (Module.End S M) x)) (m m' : M) :
    m' = (↑h.unit⁻¹ : Module.End S M) m ↔ m = x • m' where
  mp H := H ▸ (isUnit_apply_inv_apply_of_isUnit h m).symm
  mpr H := by
    apply_fun (↑h.unit : M → M) using ((isUnit_iff _).mp h).injective
    rw [H]
    simpa using isUnit_apply_inv_apply_of_isUnit h (x • m') |>.symm

