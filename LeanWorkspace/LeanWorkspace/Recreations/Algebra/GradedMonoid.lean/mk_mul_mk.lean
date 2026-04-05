import Mathlib

variable {ι : Type*}

variable (A : ι → Type*)

theorem mk_mul_mk [Add ι] [GMul A] {i j} (a : A i) (b : A j) :
    GradedMonoid.mk i a * GradedMonoid.mk j b = GradedMonoid.mk (i + j) (GMul.mul a b) := rfl

