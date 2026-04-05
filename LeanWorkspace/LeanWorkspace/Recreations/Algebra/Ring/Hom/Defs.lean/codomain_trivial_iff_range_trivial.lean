import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} (f : α →+* β)

theorem codomain_trivial_iff_range_trivial : (0 : β) = 1 ↔ ∀ x, f x = 0 := RingHom.codomain_trivial_iff_map_one_eq_zero f.trans
    ⟨fun h x => by rw [← mul_one x, RingHom.map_mul, h, mul_zero], fun h => h 1⟩

