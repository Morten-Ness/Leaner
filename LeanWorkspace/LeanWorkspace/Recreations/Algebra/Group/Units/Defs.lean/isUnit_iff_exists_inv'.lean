import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

theorem isUnit_iff_exists_inv' [Monoid M] [IsDedekindFiniteMonoid M] {a : M} :
    IsUnit a ↔ ∃ b, b * a = 1 := ⟨(·.exists_left_inv), fun ⟨b, hba⟩ ↦ .of_mul_eq_one_right b hba⟩

