import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

theorem ext_iff_trace_mul_left [NonAssocSemiring R] {A B : Matrix m n R} :
    A = B ↔ ∀ x, (x * A).trace = (x * B).trace := by
  refine ⟨fun h x => h ▸ rfl, fun h => ?_⟩
  ext i j
  classical
  simpa [Matrix.trace_single_mul] using h (single j i (1 : R))

