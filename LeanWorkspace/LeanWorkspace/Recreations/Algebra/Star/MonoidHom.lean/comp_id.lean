import Mathlib

variable {F A B C D : Type*}

variable [Monoid A] [Star A] [Monoid B] [Star B]

variable [Monoid C] [Star C] [Monoid D] [Star D]

theorem comp_id (f : A →⋆* B) : f.comp (.id _) = f := StarMonoidHom.ext fun _ => rfl

