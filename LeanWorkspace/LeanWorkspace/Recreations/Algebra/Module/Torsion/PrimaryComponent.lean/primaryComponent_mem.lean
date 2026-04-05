import Mathlib

variable {A M M₁ M₂ : Type*} [CommRing A]

variable (I : Ideal A)

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module A M] [Module A M₁]
    [Module A M₂]

theorem primaryComponent_mem (x : M) :
    x ∈ Ideal.primaryComponent M I ↔ ∃ n, x ∈ torsionBySet A M ↑(I ^ n) := by
  simp only [Ideal.primaryComponent, mem_torsionBySet_iff, SetLike.coe_sort_coe, Subtype.forall]
  constructor
  · intro a
    rw [Submodule.mem_iSup_of_directed] at a
    · simpa using a
    · intro x y
      use max x y
      simp [torsionBySet_le_torsionBySet_pow]
  · aesop (add safe Submodule.mem_iSup_of_mem)

