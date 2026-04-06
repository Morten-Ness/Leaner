import Mathlib

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem subsingleton (h : UniqueMul A B a0 b0) :
    Subsingleton { ab : G × G // ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 * ab.2 = a0 * b0 } := by
  classical
  refine ⟨?_⟩
  intro x y
  apply Subtype.ext
  rcases x with ⟨⟨x1, x2⟩, hxA, hxB, hx⟩
  rcases y with ⟨⟨y1, y2⟩, hyA, hyB, hy⟩
  dsimp at hxA hxB hx hyA hyB hy
  rcases h hxA hxB hx with ⟨rfl, rfl⟩
  rcases h hyA hyB hy with ⟨rfl, rfl⟩
  rfl
