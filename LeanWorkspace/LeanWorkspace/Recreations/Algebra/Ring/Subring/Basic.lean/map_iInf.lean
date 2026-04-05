import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem map_iInf {ι : Sort*} [Nonempty ι] (f : R →+* S) (hf : Function.Injective f)
    (s : ι → Subring R) : (iInf s).map f = ⨅ i, (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

