import Mathlib

variable {A M M₁ M₂ : Type*} [CommRing A]

variable (I : Ideal A)

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module A M] [Module A M₁]
    [Module A M₂]

theorem primaryComponent_map_mem (φ : M₁ →ₗ[A] M₂) (c : Ideal.primaryComponent M₁ I) :
    φ c ∈ Ideal.primaryComponent M₂ I := by
  obtain ⟨c, hc⟩ := c
  simp only [Ideal.primaryComponent_mem, mem_torsionBySet_iff, SetLike.coe_sort_coe, Subtype.forall,
    ← map_smul] at ⊢ hc
  obtain ⟨n, hn⟩ := hc
  use n
  grind

