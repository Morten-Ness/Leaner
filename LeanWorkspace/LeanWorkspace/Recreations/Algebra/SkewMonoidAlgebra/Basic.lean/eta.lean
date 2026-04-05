import Mathlib

variable {k G : Type*}

variable [AddMonoid k]

theorem eta (f : SkewMonoidAlgebra k G) : ofFinsupp f.toFinsupp = f := rfl

