import Mathlib

variable {R : Type uR} {S : Type uS} {ι : Type uι} {ι' : Type uι'} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} {M' : Type v'}

variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [AddCommMonoid M'] [AddCommMonoid M₂]
  [∀ i, Module R (M i)] [Module R M'] [Module R M₂]

theorem LinearMap.curryMid_uncurryMid (i : Fin (n + 1))
    (f : M i →ₗ[R] MultilinearMap R (fun j ↦ M (i.succAbove j)) M₂) :
    (f.uncurryMid i).curryMid i = f := by ext; simp

