import Mathlib

open scoped RightActions

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

theorem inl_smul [Monoid S] [AddMonoid M] [SMul S R] [DistribMulAction S M] (s : S) (r : R) :
    (TrivSqZeroExt.inl (s • r) : tsze R M) = s • TrivSqZeroExt.inl r := TrivSqZeroExt.ext rfl (smul_zero s).symm

