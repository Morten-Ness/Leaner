import Mathlib

variable {A M G α β γ : Type*}

variable {p : α → Prop} {f : Perm α}

theorem subtypePerm_apply (f : Equiv.Perm α) (h : ∀ x, p (f x) ↔ p x) (x : { x // p x }) :
    Equiv.Perm.subtypePerm f h x = ⟨f x, (h _).2 x.2⟩ := rfl

