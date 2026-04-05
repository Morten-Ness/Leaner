import Mathlib

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem AddSubmonoidClass.IsHomogeneous.mem_iff
    {P : Type*} [SetLike P M] [AddSubmonoidClass P M] (p : P)
    (hp : DirectSum.SetLike.IsHomogeneous ℳ p) {x} :
    x ∈ p ↔ ∀ i, (DirectSum.decompose ℳ x i : M) ∈ p := by
  classical
  refine ⟨fun hx i ↦ hp i hx, fun hx ↦ ?_⟩
  rw [← DirectSum.sum_support_decompose ℳ x]
  exact sum_mem (fun i _ ↦ hx i)

