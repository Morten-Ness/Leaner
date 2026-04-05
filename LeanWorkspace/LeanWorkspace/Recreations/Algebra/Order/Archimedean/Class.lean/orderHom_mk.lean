import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable {N : Type*} [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]

theorem orderHom_mk (f : M →*o N) (a : M) : MulArchimedeanClass.orderHom f (MulArchimedeanClass.mk a) = MulArchimedeanClass.mk (f a) := rfl

