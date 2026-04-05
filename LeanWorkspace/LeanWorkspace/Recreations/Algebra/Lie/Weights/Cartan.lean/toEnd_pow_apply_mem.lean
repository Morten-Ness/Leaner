import Mathlib

open scoped TensorProduct

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem toEnd_pow_apply_mem {χ₁ χ₂ : H → R} {x : L} {m : M}
    (hx : x ∈ rootSpace H χ₁) (hm : m ∈ genWeightSpace M χ₂) (n) :
    (toEnd R L M x ^ n : Module.End R M) m ∈ genWeightSpace M (n • χ₁ + χ₂) := by
  induction n with
  | zero => simpa using hm
  | succ n IH =>
    simp only [pow_succ', Module.End.mul_apply, toEnd_apply_apply]
    convert LieAlgebra.lie_mem_genWeightSpace_of_mem_genWeightSpace hx IH using 2
    rw [succ_nsmul, ← add_assoc, add_comm (n • _)]

