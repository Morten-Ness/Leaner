import Mathlib

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₁' : ι → Type v₁'} {M₁'' : ι → Type v₁''}

variable {M₂ : Type v₂} {M₃ : Type v₃} {M₄ : Type v₄} {M' : Type v'}

variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂]
  [AddCommMonoid M₃] [AddCommMonoid M'] [∀ i, Module R (M i)] [∀ i, Module R (M₁ i)] [Module R M₂]
  [Module R M₃] [Module R M'] (f f' : MultilinearMap R M₁ M₂)

theorem snoc_add (f : MultilinearMap R M M₂)
    (m : ∀ i : Fin n, M (castSucc i)) (x y : M (last n)) :
    f (snoc m (x + y)) = f (snoc m x) + f (snoc m y) := by
  simp_rw [← update_snoc_last x m (x + y), MultilinearMap.map_update_add f, update_snoc_last]

