import Mathlib

theorem well_def {R : Type*} [Rack R] {G : Type*} [Group G] (f : R →◃ Quandle.Conj G) :
    ∀ {a b : PreEnvelGroup R},
      PreEnvelGroupRel' R a b → Rack.toEnvelGroup.mapAux f a = Rack.toEnvelGroup.mapAux f b
  | _, _, PreEnvelGroupRel'.refl => rfl
  | _, _, PreEnvelGroupRel'.symm h => (well_def f h).symm
  | _, _, PreEnvelGroupRel'.trans hac hcb => Eq.trans (well_def f hac) (well_def f hcb)
  | _, _, PreEnvelGroupRel'.congr_mul ha hb => by
    simp [Rack.toEnvelGroup.mapAux, well_def f ha, well_def f hb]
  | _, _, congr_inv ha => by simp [Rack.toEnvelGroup.mapAux, well_def f ha]
  | _, _, UnitalShelf.assoc a b c => by apply mul_assoc
  | _, _, PreEnvelGroupRel'.one_mul a => by simp [Rack.toEnvelGroup.mapAux]
  | _, _, PreEnvelGroupRel'.mul_one a => by simp [Rack.toEnvelGroup.mapAux]
  | _, _, PreEnvelGroupRel'.inv_mul_cancel a => by simp [Rack.toEnvelGroup.mapAux]
  | _, _, act_incl x y => by simp [Rack.toEnvelGroup.mapAux]
