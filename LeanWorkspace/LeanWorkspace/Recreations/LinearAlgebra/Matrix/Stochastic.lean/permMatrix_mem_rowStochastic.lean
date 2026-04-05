import Mathlib

variable {R n : Type*} [Fintype n] [DecidableEq n]

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}

variable {x : n → R}

theorem permMatrix_mem_rowStochastic {σ : Equiv.Perm n} :
    σ.permMatrix R ∈ Matrix.rowStochastic R n := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?g1, ?g2⟩
  case g1 => aesop
  case g2 => simp [Equiv.toPEquiv_apply]

