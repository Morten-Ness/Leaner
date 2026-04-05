import Mathlib

section

variable {G M S : Type*}

variable [DivisionMonoid G] {a b : G}

theorem inv (hab : Commute a b) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by rw [Commute.eq hab, mul_inv_rev]

end

section

variable {G M S : Type*}

variable [Semigroup S] {a b c : S}

theorem left_comm (h : Commute a b) (c) : a * (b * c) = b * (a * c) := by
  simp only [← mul_assoc, Commute.eq h]

end

section

variable {G M S : Type*}

variable [Group G] {a b : G}

theorem mul_inv_cancel_assoc (h : Commute a b) : a * (b * a⁻¹) = b := by
  rw [← mul_assoc, Commute.mul_inv_cancel h]

end

section

variable {G M S : Type*}

variable [Monoid M] {a b : M}

theorem pow_left (h : Commute a b) (n : ℕ) : Commute (a ^ n) b := Commute.symm (Commute.pow_right h.symm n)

-- todo: should nat power be called `nsmul` here?

end

section

variable {G M S : Type*}

variable [Monoid M] {a b : M}

theorem pow_pow_self (a : M) (m n : ℕ) : Commute (a ^ m) (a ^ n) := Commute.pow_pow (Commute.refl a) m n

end

section

variable {G M S : Type*}

variable [Monoid M] {a b : M}

theorem pow_self (a : M) (n : ℕ) : Commute (a ^ n) a := Commute.pow_left (Commute.refl a) n

end

section

variable {G M S : Type*}

variable [Semigroup S] {a b c : S}

theorem right_comm (h : Commute b c) (a : S) : a * b * c = a * c * b := by
  simp only [mul_assoc, Commute.eq h]

end

section

variable {G M S : Type*}

variable [Monoid M] {a b : M}

theorem self_pow (a : M) (n : ℕ) : Commute a (a ^ n) := Commute.pow_right (Commute.refl a) n

end
