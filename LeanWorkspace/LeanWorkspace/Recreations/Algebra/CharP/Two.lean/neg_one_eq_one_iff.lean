import Mathlib

variable {R ι : Type*}

variable [Ring R]

private def sqAddMonoidHom : R →+ R where
  toFun := (· ^ 2)
  map_zero' := zero_pow two_ne_zero
  map_add' := CharTwo.add_sq


theorem neg_one_eq_one_iff [Nontrivial R] : (-1 : R) = 1 ↔ ringChar R = 2 := by
  refine ⟨fun h => ?_, fun h => @CharTwo.neg_eq _ _ (ringChar.of_eq h) 1⟩
  rw [eq_comm, ← sub_eq_zero, sub_neg_eq_add, ← Nat.cast_one, ← Nat.cast_add] at h
  exact ((Nat.dvd_prime Nat.prime_two).mp (ringChar.dvd h)).resolve_left CharP.ringChar_ne_one

