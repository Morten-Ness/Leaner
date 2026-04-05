import Mathlib

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₁' : ι → Type v₁'} {M₁'' : ι → Type v₁''}

variable {M₂ : Type v₂} {M₃ : Type v₃} {M₄ : Type v₄} {M' : Type v'}

variable [Ring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M'] [AddCommMonoid M₂]
  [∀ i, Module R (M₁ i)] [Module R M'] [Module R M₂]

theorem map_nonempty [Nonempty ι] (f : MultilinearMap R M₁ M₂) (p : ∀ i, Submodule R (M₁ i)) :
    (MultilinearMap.map f p : Set M₂).Nonempty := ⟨f 0, 0, fun i => (p i).zero_mem, rfl⟩

