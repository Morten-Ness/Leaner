import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

theorem IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteMonoid M] {a : M} (b : M) (h : a * b = 1) :
    IsUnit a := ⟨.mkOfMulEqOne a b h, rfl⟩

