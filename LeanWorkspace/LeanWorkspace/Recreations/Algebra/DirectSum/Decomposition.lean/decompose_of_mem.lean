import Mathlib

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_of_mem {x : M} {i : ι} (hx : x ∈ ℳ i) :
    DirectSum.decompose ℳ x = DirectSum.of (fun i ↦ ℳ i) i ⟨x, hx⟩ := DirectSum.decompose_coe _ ⟨x, hx⟩

