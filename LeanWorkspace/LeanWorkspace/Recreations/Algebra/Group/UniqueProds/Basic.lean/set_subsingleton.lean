import Mathlib

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem set_subsingleton (h : UniqueMul A B a0 b0) :
    Set.Subsingleton { ab : G × G | ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 * ab.2 = a0 * b0 } := by
  rintro ⟨x1, y1⟩ (hx : x1 ∈ A ∧ y1 ∈ B ∧ x1 * y1 = a0 * b0) ⟨x2, y2⟩
    (hy : x2 ∈ A ∧ y2 ∈ B ∧ x2 * y2 = a0 * b0)
  rcases h hx.1 hx.2.1 hx.2.2 with ⟨rfl, rfl⟩
  rcases h hy.1 hy.2.1 hy.2.2 with ⟨rfl, rfl⟩
  rfl

