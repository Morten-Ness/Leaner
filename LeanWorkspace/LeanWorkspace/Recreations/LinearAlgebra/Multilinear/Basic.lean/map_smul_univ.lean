import Mathlib

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₁' : ι → Type v₁'} {M₁'' : ι → Type v₁''}

variable {M₂ : Type v₂} {M₃ : Type v₃} {M₄ : Type v₄} {M' : Type v'}

variable [CommSemiring R] [∀ i, AddCommMonoid (M₁ i)] [∀ i, AddCommMonoid (M i)] [AddCommMonoid M₂]
  [∀ i, Module R (M i)] [∀ i, Module R (M₁ i)] [Module R M₂] (f f' : MultilinearMap R M₁ M₂)

theorem map_smul_univ [Fintype ι] (c : ι → R) (m : ∀ i, M₁ i) :
    (f fun i => c i • m i) = (∏ i, c i) • f m := by
  classical simpa using MultilinearMap.map_piecewise_smul f c m Finset.univ

