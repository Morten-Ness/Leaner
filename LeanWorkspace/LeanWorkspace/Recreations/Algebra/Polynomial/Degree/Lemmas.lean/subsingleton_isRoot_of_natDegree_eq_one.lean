import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]} {a : R}

theorem subsingleton_isRoot_of_natDegree_eq_one [IsLeftCancelMulZero R]
    (h : p.natDegree = 1) : { x | IsRoot p x }.Subsingleton := by
  intro r₁
  obtain ⟨r₂, hr₂, r₃, rfl⟩ : ∃ a, a ≠ 0 ∧ ∃ b, Polynomial.C a * Polynomial.X + Polynomial.C b = p := by rwa [Polynomial.natDegree_eq_one] at h
  have (x y : R) := mul_left_cancel₀ hr₂ (b := x) (c := y)
  grind [IsRoot, eval_add, eval_mul_X, eval_C]

