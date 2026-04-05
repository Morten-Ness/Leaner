import Mathlib

section

variable {α : Type u}

theorem Commute.invOf_left [Monoid α] {a b : α} [Invertible b] (h : Commute b a) :
    Commute (⅟b) a := calc
    ⅟b * a = ⅟b * (a * b * ⅟b) := by simp [mul_assoc]
    _ = ⅟b * (b * a * ⅟b) := by rw [h.eq]
    _ = a * ⅟b := by simp [mul_assoc]

end

section

variable {α : Type u}

theorem Commute.invOf_right [Monoid α] {a b : α} [Invertible b] (h : Commute a b) :
    Commute a (⅟b) := calc
    a * ⅟b = ⅟b * (b * a * ⅟b) := by simp [mul_assoc]
    _ = ⅟b * (a * b * ⅟b) := by rw [h.eq]
    _ = ⅟b * a := by simp [mul_assoc]

end

section

variable {α : Type u}

theorem IsUnit.nonempty_invertible [Monoid α] {a : α} (h : IsUnit a) : Nonempty (Invertible a) := let ⟨x, hx⟩ := h
  ⟨x.invertible.copy _ hx.symm⟩

end

section

variable {α : Type u}

theorem commute_invOf {M : Type*} [One M] [Mul M] (m : M) [Invertible m] : Commute m (⅟m) := calc
    m * ⅟m = 1 := mul_invOf_self m
    _ = ⅟m * m := (invOf_mul_self m).symm

end

section

variable {α : Type u}

variable [Monoid α]

theorem invOf_pow (m : α) [Invertible m] (n : ℕ) [Invertible (m ^ n)] : ⅟(m ^ n) = ⅟m ^ n := @invertible_unique _ _ _ _ _ (invertiblePow m n) rfl

end

section

variable {α : Type u}

theorem map_invOf {R : Type*} {S : Type*} {F : Type*} [MulOneClass R] [Monoid S]
    [FunLike F R S] [MonoidHomClass F R S] (f : F) (r : R)
    [Invertible r] [ifr : Invertible (f r)] :
    f (⅟r) = ⅟(f r) := by
  obtain rfl : ifr = Invertible.map f r := Subsingleton.elim _ _; rfl

end

section

variable {α : Type u}

theorem nonempty_invertible_iff_isUnit [Monoid α] (a : α) : Nonempty (Invertible a) ↔ IsUnit a := ⟨Nonempty.rec <| @isUnit_of_invertible _ _ _, IsUnit.nonempty_invertible⟩

end
