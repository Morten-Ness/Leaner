import Mathlib

variable {ι : Type*}

variable (A : ι → Type*)

theorem mk_pow [AddMonoid ι] [GMonoid A] {i} (a : A i) (n : ℕ) :
    GradedMonoid.mk i a ^ n = GradedMonoid.mk (n • i) (GMonoid.gnpow _ a) := rfl

