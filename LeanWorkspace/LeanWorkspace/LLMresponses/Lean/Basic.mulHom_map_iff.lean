FAIL
import Mathlib

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem mulHom_map_iff (f : G ↪ H) (mul : ∀ x y, f (x * y) = f x * f y) :
    UniqueMul (A.map f) (B.map f) (f a0) (f b0) ↔ UniqueMul A B a0 b0 := by
  constructor
  · intro h
    constructor
    · have : f a0 ∈ A.map f := h.1
      simpa [Finset.mem_map] using this
    constructor
    · have : f b0 ∈ B.map f := h.2.1
      simpa [Finset.mem_map] using this
    · intro a b ha hb hab
      have hfa : f a ∈ A.map f := by
        simpa [Finset.mem_map] using ha
      have hfb : f b ∈ B.map f := by
        simpa [Finset.mem_map] using hb
      have hmul : f a * f b = f a0 * f b0 := by
        rw [← mul, ← mul, hab]
      have hEq : f a = f a0 ∧ f b = f b0 := h.2.2 hfa hfb hmul
      exact ⟨f.injective hEq.1, f.injective hEq.2⟩
  · intro h
    constructor
    · simpa [Finset.mem_map] using h.1
    constructor
    · simpa [Finset.mem_map] using h.2.1
    · intro x y hx hy hxy
      rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
      rcases Finset.mem_map.mp hy with ⟨b, hb, rfl⟩
      have hab : a * b = a0 * b0 := by
        apply f.injective
        rw [mul, mul, hxy]
      have hEq : a = a0 ∧ b = b0 := h.2.2 ha hb hab
      exact ⟨by simpa [hEq.1], by simpa [hEq.2]⟩
