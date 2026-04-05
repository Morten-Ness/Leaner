import Mathlib

theorem toEnvelGroup.univ_uniq (R : Type*) [Rack R] (G : Type*) [Group G]
    (f : R →◃ Quandle.Conj G) (g : Rack.EnvelGroup R →* G)
    (h : f = (Quandle.Conj.map g).comp (Rack.toEnvelGroup R)) : g = Rack.toEnvelGroup.map f := h.symm ▸ (Rack.toEnvelGroup.map.apply_symm_apply g).symm

