import Mathlib

variable {G : Type*} [Group G] (H : Subgroup G)

theorem NormalizerCondition.normal_of_coatom (hnc : NormalizerCondition G) (hmax : IsCoatom H) :
    H.Normal := normalizer_eq_top_iff.mp (hmax.2 _ (hnc H (lt_top_iff_ne_top.mpr hmax.1)))

