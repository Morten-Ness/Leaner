import Mathlib

variable {A M G α β γ : Type*}

variable {p : α → Prop} {f : Perm α}

set_option backward.privateInPublic true in
private theorem inv_aux : (∀ x, p (f x) ↔ p x) ↔ ∀ x, p (f⁻¹ x) ↔ p x := f⁻¹.surjective.forall.trans <| by simp [Iff.comm]


set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem inv_subtypePerm (f : Equiv.Perm α) (hf) :
    (f.subtypePerm hf : Equiv.Perm { x // p x })⁻¹ = f⁻¹.subtypePerm (inv_aux.1 hf) := rfl

