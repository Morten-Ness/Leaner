import Mathlib

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem mulHom_map_iff (f : G ↪ H) (mul : ∀ x y, f (x * y) = f x * f y) :
    UniqueMul (A.map f) (B.map f) (f a0) (f b0) ↔ UniqueMul A B a0 b0 := by
  classical simp_rw [← UniqueMul.mulHom_image_iff ⟨f, mul⟩ f.2, Finset.map_eq_image]; rfl

