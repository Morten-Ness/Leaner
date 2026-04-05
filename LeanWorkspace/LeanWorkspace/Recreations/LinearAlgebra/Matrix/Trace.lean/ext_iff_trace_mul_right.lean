import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

theorem ext_iff_trace_mul_right [NonAssocSemiring R] {A B : Matrix m n R} :
    A = B ↔ ∀ x, (A * x).trace = (B * x).trace := by
  refine ⟨fun h x => h ▸ rfl, fun h => ?_⟩
  ext i j
  classical
  simpa [Matrix.trace_mul_single] using h (single j i (1 : R))

