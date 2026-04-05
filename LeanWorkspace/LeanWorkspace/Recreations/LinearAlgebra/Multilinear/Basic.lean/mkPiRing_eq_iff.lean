import Mathlib

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₁' : ι → Type v₁'} {M₁'' : ι → Type v₁''}

variable {M₂ : Type v₂} {M₃ : Type v₃} {M₄ : Type v₄} {M' : Type v'}

variable [CommSemiring R] [∀ i, AddCommMonoid (M₁ i)] [∀ i, AddCommMonoid (M i)] [AddCommMonoid M₂]
  [∀ i, Module R (M i)] [∀ i, Module R (M₁ i)] [Module R M₂] (f f' : MultilinearMap R M₁ M₂)

theorem mkPiRing_eq_iff [Fintype ι] {z₁ z₂ : M₂} :
    MultilinearMap.mkPiRing R ι z₁ = MultilinearMap.mkPiRing R ι z₂ ↔ z₁ = z₂ := by
  simp_rw [MultilinearMap.ext_iff, MultilinearMap.mkPiRing_apply]
  constructor <;> intro h
  · simpa using h fun _ => 1
  · simp [h]

