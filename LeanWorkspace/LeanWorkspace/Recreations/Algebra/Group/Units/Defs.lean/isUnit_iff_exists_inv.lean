import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

theorem isUnit_iff_exists_inv [Monoid M] [IsDedekindFiniteMonoid M] {a : M} :
    IsUnit a ↔ ∃ b, a * b = 1 := ⟨(·.exists_right_inv), fun ⟨b, hab⟩ ↦ .of_mul_eq_one b hab⟩

