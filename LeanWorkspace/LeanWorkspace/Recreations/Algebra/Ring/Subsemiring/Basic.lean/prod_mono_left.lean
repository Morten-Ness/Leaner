import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem prod_mono_left (t : Subsemiring S) : Monotone fun s : Subsemiring R => s.prod t := fun _ _ hs => Subsemiring.prod_mono hs (le_refl t)

