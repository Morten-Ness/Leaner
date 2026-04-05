import Mathlib

variable {α R S : Type*} {n : ℕ}

variable [NonAssocSemiring R] [NonAssocSemiring S]

theorem injective_nat (f : ℕ →+* R) [CharZero R] : Function.Injective f := Subsingleton.elim (Nat.castRingHom _) f ▸ Nat.cast_injective

