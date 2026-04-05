import Mathlib

variable {A M M₁ M₂ : Type*} [CommRing A]

variable (I : Ideal A)

variable [AddCommGroup M] [Module A M]

theorem primaryComponent_sup (N₁ N₂ : Submodule A M) (hD : Disjoint N₁ N₂) :
    (Ideal.primaryComponent ↥(N₁ ⊔ N₂) I).map (N₁ ⊔ N₂).subtype =
    (Ideal.primaryComponent N₁ I).map N₁.subtype ⊔ (Ideal.primaryComponent N₂ I).map N₂.subtype := by
  ext x
  simp_all only [mem_map, Ideal.primaryComponent_mem, mem_torsionBySet_iff, SetLike.coe_sort_coe,
    Subtype.forall, subtype_apply, Subtype.exists, SetLike.mk_smul_mk, mk_eq_zero, exists_and_left,
    exists_prop, exists_eq_right_right, Submodule.mem_sup]
  constructor
  · rintro ⟨⟨w, h⟩, ⟨y, hy, z, hz, rfl⟩⟩
    refine ⟨y, ⟨⟨w, fun a ha ↦ ?_⟩, by simp [hy]⟩, z, ⟨⟨w, fun a ha ↦ ?_⟩, by simp [hz]⟩, rfl⟩
    · exact ((Submodule.disjoint_iff_add_eq_zero.mp hD) (Submodule.smul_mem N₁ a hy)
        (Submodule.smul_mem N₂ a hz) (h a ha ▸ (smul_add a y z).symm)).1
    · exact ((Submodule.disjoint_iff_add_eq_zero.mp hD) (Submodule.smul_mem N₁ a hy)
        (Submodule.smul_mem N₂ a hz) (h a ha ▸ (smul_add a y z).symm)).2
  · rintro ⟨y, ⟨⟨n₁, hy⟩, hymem⟩, z, ⟨⟨n₂, hz⟩, hzmem⟩, rfl⟩
    constructor
    · use (max n₁ n₂)
      intro a ha
      specialize hy a (Ideal.pow_le_pow_right (by simp : n₁ ≤ max n₁ n₂) ha)
      specialize hz a (Ideal.pow_le_pow_right (by simp : n₂ ≤ max n₁ n₂) ha)
      aesop
    · use y, hymem, z, hzmem

