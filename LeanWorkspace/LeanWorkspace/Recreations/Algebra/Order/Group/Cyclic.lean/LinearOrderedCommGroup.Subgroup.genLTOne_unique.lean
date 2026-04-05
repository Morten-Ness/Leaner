import Mathlib

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]

variable (H : Subgroup G) [Nontrivial H] [hH : IsCyclic H]

theorem genLTOne_unique {g : G} (hg : g < 1) (hH : LinearOrderedCommGroup.Subgroup.zpowers g = H) : g = H.genLTOne := by
  have hg' : ¬ IsOfFinOrder g := not_isOfFinOrder_of_isMulTorsionFree (ne_of_lt hg)
  rw [← H.genLTOne_zpowers_eq_top] at hH
  rcases (LinearOrderedCommGroup.Subgroup.zpowers_eq_zpowers_iff hg').mp hH with _ | h
  · assumption
  rw [← one_lt_inv', h] at hg
  exact (not_lt_of_gt hg <| LinearOrderedCommGroup.Subgroup.genLTOne_lt_one _).elim

