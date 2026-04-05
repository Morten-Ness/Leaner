import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem inl_smul [Zero A] [SMul S R] [SMulZeroClass S A] (s : S) (r : R) :
    (Unitization.inl (s • r) : Unitization R A) = s • Unitization.inl r := Unitization.ext rfl (smul_zero s).symm

