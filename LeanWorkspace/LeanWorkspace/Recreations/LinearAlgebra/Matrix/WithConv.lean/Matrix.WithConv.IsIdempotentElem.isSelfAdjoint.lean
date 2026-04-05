import Mathlib

variable {m n α β : Type*}

theorem Matrix.WithConv.IsIdempotentElem.isSelfAdjoint [Semiring α] [IsLeftCancelMulZero α]
    [StarRing α] {f : WithConv (Matrix m n α)} (hf : IsIdempotentElem f) : IsSelfAdjoint f := by
  simp_rw [IsIdempotentElem, WithConv.ext_iff, ← Matrix.ext_iff, convMul_def, hadamard_apply,
    ← isIdempotentElem_iff, IsIdempotentElem.iff_eq_zero_or_one] at hf
  rw [IsSelfAdjoint, WithConv.ext_iff]
  ext i j
  obtain (h | h) := hf i j <;> simp_all

