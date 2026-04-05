import Mathlib

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₁' : ι → Type v₁'} {M₁'' : ι → Type v₁''}

variable {M₂ : Type v₂} {M₃ : Type v₃} {M₄ : Type v₄} {M' : Type v'}

variable [CommSemiring R] [∀ i, AddCommMonoid (M₁ i)] [∀ i, AddCommMonoid (M i)] [AddCommMonoid M₂]
  [∀ i, Module R (M i)] [∀ i, Module R (M₁ i)] [Module R M₂] (f f' : MultilinearMap R M₁ M₂)

variable [Π i, AddCommMonoid (M₁' i)] [Π i, Module R (M₁' i)]

theorem iteratedFDeriv_aux {ι} {M₁ : ι → Type*} {α : Type*} [DecidableEq α]
    (s : Set ι) [DecidableEq { x // x ∈ s }] (e : α ≃ s)
    (m : α → ((i : ι) → M₁ i)) (a : α) (z : (i : ι) → M₁ i) :
    (fun i ↦ update m a z (e.symm i) i) =
      (fun i ↦ update (fun j ↦ m (e.symm j) j) (e a) (z (e a)) i) := by
  ext i
  rcases eq_or_ne a (e.symm i) with rfl | hne
  · rw [Equiv.apply_symm_apply e i, update_self, update_self]
  · rw [update_of_ne hne.symm, update_of_ne fun h ↦ (Equiv.symm_apply_apply .. ▸ h ▸ hne) rfl]

