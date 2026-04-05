import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem vecMul_updateCol [DecidableEq n] [Fintype m] [NonUnitalNonAssocSemiring α]
    (v : m → α) (B : Matrix m n α) (j : n) (r : m → α) :
    v ᵥ* B.updateCol j r = Function.update (v ᵥ* B) j (v ⬝ᵥ r) := by
  ext j'
  obtain rfl | hj := eq_or_ne j' j
  · simp [vecMul]
  · simp [vecMul, hj]

