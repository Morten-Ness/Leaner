import Mathlib

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem set_subsingleton (h : UniqueMul A B a0 b0) :
    Set.Subsingleton { ab : G × G | ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 * ab.2 = a0 * b0 } := by
  rintro ⟨a, b⟩ ha ⟨a', b'⟩ ha'
  have hab : a = a0 ∧ b = b0 := h ha.1 ha.2.1 ha.2.2
  have ha'b' : a' = a0 ∧ b' = b0 := h ha'.1 ha'.2.1 ha'.2.2
  rcases hab with ⟨rfl, rfl⟩
  rcases ha'b' with ⟨rfl, rfl⟩
  rfl
