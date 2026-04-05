import Mathlib

variable {ιA ιB ιM : Type*}

variable (A : ιA → Type*) (M : ιM → Type*)

theorem mk_smul_mk [VAdd ιA ιM] [GSMul A M] {i j} (a : A i) (b : M j) :
    GradedMonoid.mk i a • GradedMonoid.mk j b = GradedMonoid.mk (i +ᵥ j) (GSMul.smul a b) := rfl

