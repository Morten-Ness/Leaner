import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

theorem toSubmonoid_injective : (fun s : Subring R => s.toSubmonoid).Injective := fun _ _ h ↦ SetLike.ext (SetLike.ext_iff.mp h :)

