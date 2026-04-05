import Mathlib

variable {M M₂ : Type*}

theorem map_nnratCast_smul [AddCommMonoid M] [AddCommMonoid M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [DivisionSemiring R] [DivisionSemiring S]
    [Module R M] [Module S M₂] (c : ℚ≥0) (x : M) :
    f ((c : R) • x) = (c : S) • f x := by
  rw [NNRat.cast_def, NNRat.cast_def, div_eq_mul_inv, div_eq_mul_inv, mul_smul, mul_smul,
    map_natCast_smul f R S, map_inv_natCast_smul f R S]

