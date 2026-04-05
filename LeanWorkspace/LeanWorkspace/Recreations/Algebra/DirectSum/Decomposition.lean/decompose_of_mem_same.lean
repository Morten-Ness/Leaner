import Mathlib

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_of_mem_same {x : M} {i : ι} (hx : x ∈ ℳ i) : (DirectSum.decompose ℳ x i : M) = x := by
  rw [DirectSum.decompose_of_mem _ hx, DirectSum.of_eq_same, Subtype.coe_mk]

