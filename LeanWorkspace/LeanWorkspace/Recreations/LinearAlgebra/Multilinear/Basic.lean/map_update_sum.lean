import Mathlib

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₁' : ι → Type v₁'} {M₁'' : ι → Type v₁''}

variable {M₂ : Type v₂} {M₃ : Type v₃} {M₄ : Type v₄} {M' : Type v'}

variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂]
  [AddCommMonoid M₃] [AddCommMonoid M'] [∀ i, Module R (M i)] [∀ i, Module R (M₁ i)] [Module R M₂]
  [Module R M₃] [Module R M'] (f f' : MultilinearMap R M₁ M₂)

variable {α : ι → Type*} (g : ∀ i, α i → M₁ i) (A : ∀ i, Finset (α i))

theorem map_update_sum {α : Type*} [DecidableEq ι] (t : Finset α) (i : ι) (g : α → M₁ i)
    (m : ∀ i, M₁ i) : f (update m i (∑ a ∈ t, g a)) = ∑ a ∈ t, f (update m i (g a)) := by
  classical
    induction t using Finset.induction with
    | empty => simp
    | insert _ _ has ih => simp [Finset.sum_insert has, ih]

