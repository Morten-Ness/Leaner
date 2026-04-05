import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem reflect_support (N : ℕ) (f : R[X]) :
    (Polynomial.reflect N f).support = Finset.image (Polynomial.revAt N) f.support := by
  rcases f with ⟨⟩
  ext1
  simp only [Polynomial.reflect, support_ofFinsupp, support_embDomain, Finset.mem_map, Finset.mem_image]

