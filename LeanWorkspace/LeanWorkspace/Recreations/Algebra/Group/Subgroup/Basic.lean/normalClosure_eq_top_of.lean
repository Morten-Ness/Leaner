import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem normalClosure_eq_top_of {N : Subgroup G} [hn : N.Normal] {g g' : G} {hg : g ∈ N}
    {hg' : g' ∈ N} (hc : IsConj g g') (ht : Subgroup.normalClosure ({⟨g, hg⟩} : Set N) = ⊤) :
    Subgroup.normalClosure ({⟨g', hg'⟩} : Set N) = ⊤ := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  have h : ∀ x : N, (MulAut.conj c) x ∈ N := by
    rintro ⟨x, hx⟩
    exact hn.conj_mem _ hx c
  have hs : Function.Surjective (((MulAut.conj c).toMonoidHom.restrict N).codRestrict _ h) := by
    rintro ⟨x, hx⟩
    refine ⟨⟨c⁻¹ * x * c, ?_⟩, ?_⟩
    · have h := hn.conj_mem _ hx c⁻¹
      rwa [inv_inv] at h
    simp only [MonoidHom.codRestrict_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.restrict_apply, Subtype.mk_eq_mk, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [mul_assoc, mul_inv_cancel, mul_one]
  rw [eq_top_iff, ← MonoidHom.range_eq_top.2 hs, MonoidHom.range_eq_map]
  grw [eq_top_iff.1 ht]
  refine map_le_iff_le_comap.2 (Subgroup.normalClosure_le_normal ?_)
  rw [Set.singleton_subset_iff, SetLike.mem_coe]
  simp only [MonoidHom.codRestrict_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    MonoidHom.restrict_apply, mem_comap]
  exact Subgroup.subset_normalClosure (Set.mem_singleton _)

