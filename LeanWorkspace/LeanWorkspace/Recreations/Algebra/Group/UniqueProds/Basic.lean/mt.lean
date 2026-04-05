import Mathlib

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem mt (h : UniqueMul A B a0 b0) :
    ∀ ⦃a b⦄, a ∈ A → b ∈ B → a ≠ a0 ∨ b ≠ b0 → a * b ≠ a0 * b0 := fun _ _ ha hb k ↦ by
  contrapose! k
  exact h ha hb k

