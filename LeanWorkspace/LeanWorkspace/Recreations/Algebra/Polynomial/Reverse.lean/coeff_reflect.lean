import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem coeff_reflect (N : ℕ) (f : R[X]) (i : ℕ) : coeff (Polynomial.reflect N f) i = f.coeff (Polynomial.revAt N i) := by
  rcases f with ⟨f⟩
  simp only [Polynomial.reflect, coeff]
  calc
    Finsupp.embDomain (Polynomial.revAt N) f i = Finsupp.embDomain (Polynomial.revAt N) f (Polynomial.revAt N (Polynomial.revAt N i)) := by
      rw [Polynomial.revAt_invol]
    _ = f (Polynomial.revAt N i) := Finsupp.embDomain_apply_self _ _ _

