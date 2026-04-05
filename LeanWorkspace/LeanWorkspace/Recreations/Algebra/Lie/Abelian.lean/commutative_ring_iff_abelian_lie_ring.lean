import Mathlib

theorem commutative_ring_iff_abelian_lie_ring {A : Type v} [Ring A] :
    Std.Commutative (α := A) (· * ·) ↔ IsLieAbelian A := by
  have h₁ : Std.Commutative (α := A) (· * ·) ↔ ∀ a b : A, a * b = b * a :=
    ⟨fun h => h.1, fun h => ⟨h⟩⟩
  have h₂ : IsLieAbelian A ↔ ∀ a b : A, ⁅a, b⁆ = 0 := ⟨fun h => h.1, fun h => ⟨h⟩⟩
  simp only [h₁, h₂, LieRing.of_associative_ring_bracket, sub_eq_zero]

