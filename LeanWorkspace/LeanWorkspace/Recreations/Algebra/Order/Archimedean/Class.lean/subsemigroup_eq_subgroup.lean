import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable {N : Type*} [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]

variable {s : UpperSet (FiniteMulArchimedeanClass M)}

theorem subsemigroup_eq_subgroup :
    MulArchimedeanClass.subsemigroup (FiniteMulArchimedeanClass.toUpperSetMulArchimedeanClass s) = (FiniteMulArchimedeanClass.subgroup s : Set M) := rfl

