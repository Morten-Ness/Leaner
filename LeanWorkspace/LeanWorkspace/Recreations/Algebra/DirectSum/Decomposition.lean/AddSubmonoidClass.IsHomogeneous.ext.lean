import Mathlib

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem AddSubmonoidClass.IsHomogeneous.ext
    {ℳ : ι → σ} [Decomposition ℳ] {P : Type*} [SetLike P M] [AddSubmonoidClass P M]
    {p q : P} (hp : DirectSum.SetLike.IsHomogeneous ℳ p) (hq : DirectSum.SetLike.IsHomogeneous ℳ q)
    (hpq : ∀ i, ∀ m ∈ ℳ i, m ∈ p ↔ m ∈ q) :
    p = q := by
  refine SetLike.ext fun m ↦ ?_
  rw [DirectSum.AddSubmonoidClass.IsHomogeneous.mem_iff ℳ p hp,
    DirectSum.AddSubmonoidClass.IsHomogeneous.mem_iff ℳ q hq]
  exact forall_congr' fun i ↦ hpq i _ (DirectSum.decompose ℳ _ i).2

