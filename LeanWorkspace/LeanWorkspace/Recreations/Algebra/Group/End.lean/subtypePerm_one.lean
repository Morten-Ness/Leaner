import Mathlib

variable {A M G α β γ : Type*}

variable {p : α → Prop} {f : Perm α}

theorem subtypePerm_one (p : α → Prop) (h := fun _ => Iff.rfl) : @Equiv.Perm.subtypePerm α p 1 h = 1 :=
  rfl

