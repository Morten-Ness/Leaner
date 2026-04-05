import Mathlib

variable {A M M₁ M₂ : Type*} [CommRing A]

variable (I : Ideal A)

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module A M] [Module A M₁]
    [Module A M₂]

theorem primaryComponent_torsionBySet_of_isCoprime (J : Ideal A) (hD : IsCoprime I J) :
    Ideal.primaryComponent (torsionBySet A M J) I = ⊥ := by
  have (n : ℕ) : Disjoint (torsionBySet A M ↑(I ^ n)) (torsionBySet A M ↑J) :=
    Submodule.disjoint_torsionBySet_ideal (M := M) (Ideal.pow_sup_eq_top hD.sup_eq)
  apply Submodule.map_injective_of_injective (Submodule.subtype_injective (torsionBySet A M ↑J))
  ext x
  simp only [mem_map, Ideal.primaryComponent_mem, mem_torsionBySet_iff, SetLike.coe_sort_coe,
    Subtype.forall, subtype_apply, Subtype.exists, SetLike.mk_smul_mk, mk_eq_zero, exists_and_left,
    exists_prop, exists_eq_right_right, Submodule.map_bot, Submodule.mem_bot]
  refine ⟨fun ⟨⟨n, _⟩, _⟩ ↦ ?_, by simp_all⟩
  specialize this n
  simp_all [disjoint_def]

