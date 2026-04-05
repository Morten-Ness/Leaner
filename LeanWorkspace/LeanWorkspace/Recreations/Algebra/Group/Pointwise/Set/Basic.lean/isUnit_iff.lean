import Mathlib

variable {F α β γ : Type*}

variable [DivisionMonoid α] {s t : Set α} {n : ℤ}

theorem isUnit_iff : IsUnit s ↔ ∃ a, s = {a} ∧ IsUnit a := by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨a, b, ha, hb, h⟩ := Set.mul_eq_one_iff.1 u.mul_inv
    refine ⟨a, ha, ⟨a, b, h, singleton_injective ?_⟩, rfl⟩
    rw [← Set.singleton_mul_singleton, ← ha, ← hb]
    exact u.inv_mul
  · rintro ⟨a, rfl, ha⟩
    exact ha.set

