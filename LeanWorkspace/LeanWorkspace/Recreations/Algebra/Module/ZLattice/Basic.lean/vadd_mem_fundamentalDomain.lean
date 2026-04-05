import Mathlib

variable {E ι : Type*}

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

variable [LinearOrder K]

variable [IsStrictOrderedRing K]

variable [FloorRing K]

theorem vadd_mem_fundamentalDomain [Fintype ι] (y : span ℤ (Set.range b)) (x : E) :
    y +ᵥ x ∈ ZSpan.fundamentalDomain b ↔ y = -ZSpan.floor b x := by
  rw [Subtype.ext_iff, ← add_right_inj x, NegMemClass.coe_neg, ← sub_eq_add_neg, ← ZSpan.fract_apply,
    ← ZSpan.fract_zSpan_add b _ (Subtype.mem y), add_comm, ← vadd_eq_add, ← vadd_def, eq_comm, ←
    ZSpan.fract_eq_self]

