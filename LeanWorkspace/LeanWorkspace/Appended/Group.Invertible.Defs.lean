import Mathlib

section

variable {α : Type u}

theorem invOf_eq_group_inv [Group α] (a : α) [Invertible a] : ⅟a = a⁻¹ := invOf_eq_right_inv (mul_inv_cancel a)

end

section

variable {α : Type u}

variable [Monoid α] (a b : α)

theorem invOf_eq_iff_left [Invertible a] : ⅟a = b ↔ b * a = 1 := ⟨fun h ↦ by rw [← h, invOf_mul_self], invOf_eq_left_inv⟩

end

section

variable {α : Type u}

variable [Monoid α] (a b : α)

theorem invOf_eq_iff_right [Invertible a] : ⅟a = b ↔ a * b = 1 := ⟨fun h ↦ by rw [← h, mul_invOf_self], invOf_eq_right_inv⟩

end

section

variable {α : Type u}

variable [Monoid α] (a b : α)

theorem invOf_eq_left_inv [Invertible a] (hac : b * a = 1) : ⅟a = b := (left_inv_eq_right_inv hac (mul_invOf_self _)).symm

end

section

variable {α : Type u}

variable [Monoid α] (a b : α)

theorem invOf_eq_right_inv [Invertible a] (hac : a * b = 1) : ⅟a = b := left_inv_eq_right_inv (invOf_mul_self _) hac

end

section

variable {α : Type u}

theorem invOf_inj [Monoid α] {a b : α} [Invertible a] [Invertible b] : ⅟a = ⅟b ↔ a = b := ⟨invertible_unique _ _, invertible_unique _ _⟩

end

section

variable {α : Type u}

theorem invOf_invOf [Monoid α] (a : α) [Invertible a] [Invertible (⅟a)] : ⅟(⅟a) = a := invOf_eq_right_inv (invOf_mul_self _)

end

section

variable {α : Type u}

theorem invOf_mul [Monoid α] (a b : α) [Invertible a] [Invertible b] [Invertible (a * b)] :
    ⅟(a * b) = ⅟b * ⅟a := invOf_eq_right_inv (by simp [← mul_assoc])

end

section

variable {α : Type u}

variable [Monoid α] (a b : α)

theorem invOf_mul_cancel_left' {_ : Invertible a} : ⅟a * (a * b) = b := by
  rw [← mul_assoc, invOf_mul_self, one_mul]
example {G} [Group G] (a b : G) : a⁻¹ * (a * b) = b := inv_mul_cancel_left a b

end

section

variable {α : Type u}

variable [Monoid α] (a b : α)

theorem invOf_mul_cancel_right' {_ : Invertible b} : a * ⅟b * b = a := by
  simp [mul_assoc]
example {G} [Group G] (a b : G) : a * b⁻¹ * b = a := inv_mul_cancel_right a b

end

section

variable {α : Type u}

variable [Monoid α] {a b c : α} [Invertible c]

theorem invOf_mul_eq_iff_eq_mul_left : ⅟c * a = b ↔ a = c * b := by
  rw [← mul_right_inj_of_invertible (c := c), mul_invOf_cancel_left]

end

section

variable {α : Type u}

variable [Monoid α] (a b : α)

theorem invertible_unique [Invertible a] [Invertible b]
    (h : a = b) : ⅟a = ⅟b := by
  apply invOf_eq_right_inv
  rw [h, mul_invOf_self]

end

section

variable {α : Type u}

variable [Monoid α] (a b : α)

theorem mul_invOf_cancel_left' {_ : Invertible a} : a * (⅟a * b) = b := by
  rw [← mul_assoc, mul_invOf_self, one_mul]
example {G} [Group G] (a b : G) : a * (a⁻¹ * b) = b := mul_inv_cancel_left a b

end

section

variable {α : Type u}

variable [Monoid α] (a b : α)

theorem mul_invOf_cancel_right' {_ : Invertible b} : a * b * ⅟b = a := by
  simp [mul_assoc]
example {G} [Group G] (a b : G) : a * b * b⁻¹ = a := mul_inv_cancel_right a b

end

section

variable {α : Type u}

variable [Monoid α] {a b c : α} [Invertible c]

theorem mul_invOf_eq_iff_eq_mul_right : a * ⅟c = b ↔ a = b * c := by
  rw [← mul_left_inj_of_invertible (c := c), invOf_mul_cancel_right]

end

section

variable {α : Type u}

variable [Monoid α] {a b c : α} [Invertible c]

theorem mul_left_eq_iff_eq_invOf_mul : c * a = b ↔ a = ⅟c * b := by
  rw [← mul_right_inj_of_invertible (c := ⅟c), invOf_mul_cancel_left]

end

section

variable {α : Type u}

variable [Monoid α] {a b c : α} [Invertible c]

theorem mul_left_inj_of_invertible : a * c = b * c ↔ a = b := ⟨fun h => by simpa using congr_arg (· * ⅟c) h, congr_arg (· * _)⟩

end

section

variable {α : Type u}

variable [Monoid α] {a b c : α} [Invertible c]

theorem mul_right_eq_iff_eq_mul_invOf : a * c = b ↔ a = b * ⅟c := by
  rw [← mul_left_inj_of_invertible (c := ⅟c), mul_invOf_cancel_right]

end

section

variable {α : Type u}

variable [Monoid α] {a b c : α} [Invertible c]

theorem mul_right_inj_of_invertible : c * a = c * b ↔ a = b := ⟨fun h => by simpa using congr_arg (⅟c * ·) h, congr_arg (_ * ·)⟩

end
