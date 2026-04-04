import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

theorem affineSpan_pair_parallel_iff_exists_unit_smul' [IsDomain k] [Module.IsTorsionFree k V]
    {p₁ q₁ p₂ q₂ : P} :
    line[k, p₁, q₁] ∥ line[k, p₂, q₂] ↔ ∃ z : kˣ, z • (q₁ -ᵥ p₁) = q₂ -ᵥ p₂ := by
  rw [AffineSubspace.affineSpan_pair_parallel_iff_vectorSpan_eq, vectorSpan_pair_rev,
    vectorSpan_pair_rev, Submodule.span_singleton_eq_span_singleton]

