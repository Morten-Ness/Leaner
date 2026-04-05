import Mathlib

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₁' : ι → Type v₁'} {M₁'' : ι → Type v₁''}

variable {M₂ : Type v₂} {M₃ : Type v₃} {M₄ : Type v₄} {M' : Type v'}

variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂]
  [AddCommMonoid M₃] [AddCommMonoid M'] [∀ i, Module R (M i)] [∀ i, Module R (M₁ i)] [Module R M₂]
  [Module R M₃] [Module R M'] (f f' : MultilinearMap R M₁ M₂)

theorem map_insertNth_smul (f : MultilinearMap R M M₂) (p : Fin (n + 1))
    (m : ∀ i, M (p.succAbove i)) (c : R) (x : M p) :
    f (p.insertNth (c • x) m) = c • f (p.insertNth x m) := by
  simpa using MultilinearMap.map_update_smul f (p.insertNth 0 m) p c x

