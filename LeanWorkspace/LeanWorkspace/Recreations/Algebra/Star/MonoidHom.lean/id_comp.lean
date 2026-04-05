import Mathlib

variable {F A B C D : Type*}

variable [Monoid A] [Star A] [Monoid B] [Star B]

variable [Monoid C] [Star C] [Monoid D] [Star D]

theorem id_comp (f : A →⋆* B) : (StarMonoidHom.id B).comp f = f := StarMonoidHom.ext fun _ => rfl

