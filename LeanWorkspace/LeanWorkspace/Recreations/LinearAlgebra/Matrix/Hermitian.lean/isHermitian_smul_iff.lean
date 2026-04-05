import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable {R : Type*} [Monoid R] [Star R] [Star α] [MulAction R α] [StarModule R α]

theorem isHermitian_smul_iff {A : Matrix n n α} {k : R} [Invertible k] (hk : IsSelfAdjoint k) :
    (k • A).IsHermitian ↔ A.IsHermitian := ⟨(·.of_smul hk), (·.smul hk)⟩

