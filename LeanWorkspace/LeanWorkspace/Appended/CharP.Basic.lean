import Mathlib

section

variable (R : Type*)

theorem charZero_iff_forall_prime_ne_zero [NonAssocRing R] [NoZeroDivisors R] [Nontrivial R] :
    CharZero R ↔ ∀ p : ℕ, p.Prime → (p : R) ≠ 0 := by
  refine ⟨fun h p hp => by simp [hp.ne_zero], fun h => ?_⟩
  let p := ringChar R
  cases CharP.char_is_prime_or_zero R p with
  | inl hp => simpa using h p hp
  | inr h => have : CharP R 0 := h ▸ inferInstance; exact CharP.charP_to_charZero R

end

section

variable (R : Type*)

variable [AddGroupWithOne R] (p : ℕ) [CharP R p] {a b : ℤ}

theorem intCast_eq_intCast : (a : R) = b ↔ a ≡ b [ZMOD p] := by
  rw [eq_comm, ← sub_eq_zero, ← Int.cast_sub, CharP.intCast_eq_zero_iff R p, Int.modEq_iff_dvd]

end

section

variable (R : Type*)

variable [AddGroupWithOne R] (p : ℕ) [CharP R p] {a b : ℤ}

theorem intCast_eq_intCast_mod : (a : R) = a % (p : ℤ) := (CharP.intCast_eq_intCast R p).mpr (Int.mod_modEq a p).symm

end

section

variable (R : Type*)

variable [AddMonoidWithOne R] (p : ℕ)

variable [CharP R p] {a b : ℕ}

theorem natCast_eq_natCast_mod (a : ℕ) : (a : R) = a % p := CharP.natCast_eq_natCast' R p (Nat.mod_modEq a p).symm

end

section

variable (R : Type*)

variable [AddMonoidWithOne R] (p : ℕ)

variable [CharP R p] {a b : ℕ}

variable [IsRightCancelAdd R]

theorem natCast_injOn_Iio : (Set.Iio p).InjOn ((↑) : ℕ → R) := fun _a ha _b hb hab ↦ ((CharP.natCast_eq_natCast _ _).1 hab).eq_of_lt_of_lt ha hb

end
