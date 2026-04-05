import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

set_option backward.isDefEq.respectTransparency false in
theorem updateRow_zero_mul_updateCol_zero
    [DecidableEq l] [DecidableEq n] [Fintype m] [NonUnitalNonAssocSemiring α]
    (i : l) (r : m → α) (j : n) (c : m → α) :
    (0 : Matrix l m α).updateRow i r * (0 : Matrix m n α).updateCol j c = single i j (r ⬝ᵥ c) := by
  rw [Matrix.updateRow_mul, Matrix.vecMul_updateCol, Matrix.mul_updateCol, single_eq_of_single_single, Matrix.zero_mul,
    vecMul_zero, zero_mulVec, Matrix.updateCol_zero_zero, Matrix.updateRow, ← Pi.single, ← Pi.single]

