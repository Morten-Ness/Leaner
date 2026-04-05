import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem map_comap_eq_self_of_surjective
    {f : R →+* S} (hf : Function.Surjective f) (t : Subsemiring S) : (t.comap f).map f = t := Subsemiring.map_comap_eq_self <| by simp [hf]

