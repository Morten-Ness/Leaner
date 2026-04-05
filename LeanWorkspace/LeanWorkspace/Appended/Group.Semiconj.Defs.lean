import Mathlib

section

variable {S M G : Type*}

variable [Group G]

theorem conj_iff {a x y b : G} :
    SemiconjBy (b * a * b⁻¹) (b * x * b⁻¹) (b * y * b⁻¹) ↔ SemiconjBy a x y := by
  unfold SemiconjBy
  simp only [← mul_assoc, inv_mul_cancel_right]
  repeat rw [mul_assoc]
  rw [mul_left_cancel_iff, ← mul_assoc, ← mul_assoc, mul_right_cancel_iff]

end

section

variable {S M G : Type*}

variable [Group G]

theorem conj_mk (a x : G) : SemiconjBy a x (a * x * a⁻¹) := by
  unfold SemiconjBy; rw [mul_assoc, inv_mul_cancel, mul_one]

end

section

variable {S M G : Type*}

variable [Semigroup S] {a b x y z x' y' : S}

theorem isTrans : IsTrans S fun a b ↦ ∃ c, SemiconjBy c a b := ⟨fun _ _ _ ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨y * x, SemiconjBy.mul_left hy hx⟩⟩

end

section

variable {S M G : Type*}

variable [Semigroup S] {a b x y z x' y' : S}

theorem mul_left (ha : SemiconjBy a y z) (hb : SemiconjBy b x y) : SemiconjBy (a * b) x z := by
  unfold SemiconjBy
  rw [mul_assoc, SemiconjBy.eq hb, ← mul_assoc, SemiconjBy.eq ha, mul_assoc]

end

section

variable {S M G : Type*}

variable [Semigroup S] {a b x y z x' y' : S}

theorem mul_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x * x') (y * y') := by
  unfold SemiconjBy
  -- TODO this could be done using `assoc_rw` if/when this is ported to mathlib4
  rw [← mul_assoc, SemiconjBy.eq h, mul_assoc, SemiconjBy.eq h', ← mul_assoc]

end

section

variable {S M G : Type*}

variable [MulOneClass M]

theorem one_right (a : M) : SemiconjBy a 1 1 := by rw [SemiconjBy, mul_one, one_mul]

end

section

variable {S M G : Type*}

variable [Monoid M]

theorem pow_right {a x y : M} (h : SemiconjBy a x y) (n : ℕ) : SemiconjBy a (x ^ n) (y ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact SemiconjBy.one_right _
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact SemiconjBy.mul_right ih h

end
