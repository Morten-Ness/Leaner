import Mathlib

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₁' : ι → Type v₁'} {M₁'' : ι → Type v₁''}

variable {M₂ : Type v₂} {M₃ : Type v₃} {M₄ : Type v₄} {M' : Type v'}

variable [CommSemiring R] [∀ i, AddCommMonoid (M₁ i)] [∀ i, AddCommMonoid (M i)] [AddCommMonoid M₂]
  [∀ i, Module R (M i)] [∀ i, Module R (M₁ i)] [Module R M₂] (f f' : MultilinearMap R M₁ M₂)

theorem ext_ring [Finite ι] ⦃f g : MultilinearMap R (fun _ : ι => R) M₂⦄
    (h : f (fun _ ↦ 1) = g (fun _ ↦ 1)) : f = g := by
  ext x
  obtain ⟨_⟩ := nonempty_fintype ι
  have hf := MultilinearMap.map_smul_univ f x (fun _ ↦ 1)
  have hg := MultilinearMap.map_smul_univ g x (fun _ ↦ 1)
  simp_all

