import Mathlib

variable {A M G α β γ : Type*}

variable {p : α → Prop} {f : Perm α}

theorem subtypePerm_mul (f g : Equiv.Perm α) (hf hg) :
    (f.subtypePerm hf * g.subtypePerm hg : Equiv.Perm { x // p x }) =
      (f * g).subtypePerm fun _ => (hf _).trans <| hg _ := rfl

