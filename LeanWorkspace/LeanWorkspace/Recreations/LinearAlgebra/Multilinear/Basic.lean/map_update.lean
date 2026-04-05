import Mathlib

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₁' : ι → Type v₁'} {M₁'' : ι → Type v₁''}

variable {M₂ : Type v₂} {M₃ : Type v₃} {M₄ : Type v₄} {M' : Type v'}

variable [Semiring R] [∀ i, AddCommGroup (M₁ i)] [AddCommGroup M₂] [∀ i, Module R (M₁ i)]
  [Module R M₂] (f : MultilinearMap R M₁ M₂)

theorem map_update [DecidableEq ι] (x : (i : ι) → M₁ i) (i : ι) (v : M₁ i) :
    f (update x i v) = f x - f (update x i (x i - v)) := by
  rw [MultilinearMap.map_update_sub, update_eq_self, sub_sub_cancel]

