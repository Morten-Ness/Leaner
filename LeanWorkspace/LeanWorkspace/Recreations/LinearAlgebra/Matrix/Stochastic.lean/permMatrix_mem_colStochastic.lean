import Mathlib

variable {R n : Type*} [Fintype n] [DecidableEq n]

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}

variable {x : n → R}

theorem permMatrix_mem_colStochastic {σ : Equiv.Perm n} :
    σ.permMatrix R ∈ Matrix.colStochastic R n := by
  rw [Matrix.mem_colStochastic_iff_sum]
  refine ⟨fun i j => ?g1, ?g2⟩
  case g1 => aesop
  case g2 => simp [Equiv.toPEquiv_apply, ← Equiv.eq_symm_apply]

