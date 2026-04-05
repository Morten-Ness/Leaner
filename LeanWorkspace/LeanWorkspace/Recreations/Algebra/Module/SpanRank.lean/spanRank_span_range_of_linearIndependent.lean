import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem spanRank_span_range_of_linearIndependent [RankCondition R] {ι : Type u} {v : ι → M}
    (hv : v.Injective) (hs : LinearIndependent R v) :
    (span R (.range v)).spanRank = #ι := by
  refine le_antisymm (le_trans (Submodule.spanRank_span_le_card _) mk_range_le) (le_ciInf fun x ↦ ?_)
  have : #x.1 = #((Subtype.val : span R (.range v) → _) ⁻¹' x.1) :=
    (mk_preimage_of_injective_of_subset_range _ _ Subtype.val_injective (by simp [← x.2])).symm
  rw [this]
  refine le_trans ?_ ((Module.Basis.span hs).le_span (R := R) (J := Subtype.val ⁻¹' x.1) ?_)
  · rw [mk_range_eq]
    exact .of_comp (f := Subtype.val) (by convert hv; ext; simp [Module.Basis.span_apply])
  · apply map_injective_of_injective (f := (span R _).subtype) (injective_subtype _)
    simp [map_span, Set.image_preimage_eq_inter_range, Set.inter_eq_self_of_subset_left, ← x.2]

