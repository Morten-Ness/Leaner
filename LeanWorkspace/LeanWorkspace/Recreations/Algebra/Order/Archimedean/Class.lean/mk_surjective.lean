import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_surjective : Function.Surjective <| MulArchimedeanClass.mk (M := M) := Quotient.mk_surjective

