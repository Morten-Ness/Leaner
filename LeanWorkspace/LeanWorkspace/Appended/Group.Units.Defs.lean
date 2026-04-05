import Mathlib

section

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [DivisionMonoid α] {a b c : α}

theorem inv (h : IsUnit a) : IsUnit a⁻¹ := by
  obtain ⟨u, hu⟩ := h
  rw [← hu, ← Units.val_inv_eq_inv_val]
  exact Units.isUnit _

end

section

variable {α : Type u}

variable {M : Type*} {N : Type*}

theorem mul_iff [Monoid M] [IsDedekindFiniteMonoid M] {x y : M} :
    IsUnit (x * y) ↔ IsUnit x ∧ IsUnit y := ⟨fun h => ⟨isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩,
   fun h => IsUnit.mul h.1 h.2⟩

end

section

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [Monoid M] {a b : M}

theorem mul_left_iff {a b : M} (ha : IsUnit a) :
    IsUnit (a * b) ↔ IsUnit b := show IsUnit (ha.unit * b) ↔ _ by simp [- IsUnit.unit_spec]

grind_pattern mul_left_iff => IsUnit a, IsUnit (a * b)

end

section

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [Monoid M] {a b : M}

theorem mul_right_iff {a b : M} (hb : IsUnit b) :
    IsUnit (a * b) ↔ IsUnit a := show IsUnit (a * hb.unit) ↔ _ by simp [- IsUnit.unit_spec]

grind_pattern mul_right_iff => IsUnit b, IsUnit (a * b)

end

section

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [Monoid M] {a b : M}

theorem mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1 := by
  rw [← Units.mul_inv h.unit]; congr

end

section

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [DivisionMonoid α] {a b c : α}

theorem unit_div (ha : IsUnit a) (hb : IsUnit b) : (IsUnit.div ha hb).unit = ha.unit / hb.unit := Units.ext (Units.val_div_eq_div_val ha.unit hb.unit).symm

end

section

variable {α : Type u}

variable [Monoid α]

variable (a b : αˣ) {u : αˣ}

theorem val_eq_one {a : αˣ} : (a : α) = 1 ↔ a = 1 := by rw [← Units.val_one, Units.val_inj]

end
