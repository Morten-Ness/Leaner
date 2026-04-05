import Mathlib

variable {R : Type*} [Semiring R] (p q : R[X])

theorem mirror_eq_zero : p.mirror = 0 ↔ p = 0 := ⟨fun h => by rw [← Polynomial.mirror_mirror p, h, Polynomial.mirror_zero], fun h => by rw [h, Polynomial.mirror_zero]⟩

