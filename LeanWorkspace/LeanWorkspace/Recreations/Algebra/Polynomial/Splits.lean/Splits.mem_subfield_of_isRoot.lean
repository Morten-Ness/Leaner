import Mathlib

variable {R : Type*}

variable [Field R] {f g : R[X]}

theorem Splits.mem_subfield_of_isRoot (F : Subfield R) {f : F[X]} (hf : Polynomial.Splits f) (hf0 : f ≠ 0)
    {x : R} (hx : (f.map F.subtype).IsRoot x) : x ∈ F := by
  simpa using hf.mem_range_of_isRoot hf0 hx

