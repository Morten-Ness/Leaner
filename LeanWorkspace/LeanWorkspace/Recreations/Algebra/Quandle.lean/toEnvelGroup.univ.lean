import Mathlib

theorem toEnvelGroup.univ (R : Type*) [Rack R] (G : Type*) [Group G] (f : R →◃ Quandle.Conj G) :
    (Quandle.Conj.map (Rack.toEnvelGroup.map f)).comp (Rack.toEnvelGroup R) = f := Rack.toEnvelGroup.map.symm_apply_apply f

