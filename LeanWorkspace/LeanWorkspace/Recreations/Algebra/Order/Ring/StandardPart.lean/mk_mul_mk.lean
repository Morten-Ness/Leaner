import Mathlib

theorem mk_mul_mk (x y : K) (hx hy) :
    .mk x hx * .mk y hy = ArchimedeanClass.FiniteElement.mk (x * y) (add_nonneg hx hy) := rfl

