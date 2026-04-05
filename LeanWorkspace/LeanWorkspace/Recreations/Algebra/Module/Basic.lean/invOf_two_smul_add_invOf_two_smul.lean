import Mathlib

variable {α R M M₂ : Type*}

theorem invOf_two_smul_add_invOf_two_smul (R) [Semiring R] [AddCommMonoid M] [Module R M]
    [Invertible (2 : R)] (x : M) :
    (⅟2 : R) • x + (⅟2 : R) • x = x := Convex.combo_self invOf_two_add_invOf_two _

