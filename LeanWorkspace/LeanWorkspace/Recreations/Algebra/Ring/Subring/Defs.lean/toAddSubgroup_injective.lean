import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

theorem toAddSubgroup_injective : (toAddSubgroup : Subring R → AddSubgroup R).Injective := fun _ _ h ↦ SetLike.ext (SetLike.ext_iff.mp h :)

