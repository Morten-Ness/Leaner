import Mathlib

variable {A M G α β γ : Type*}

variable {p : α → Prop} {f : Perm α}

set_option backward.privateInPublic true in
private theorem inv_aux : (∀ x, p (f x) ↔ p x) ↔ ∀ x, p (f⁻¹ x) ↔ p x := f⁻¹.surjective.forall.trans <| by simp [Iff.comm]


set_option backward.privateInPublic true in
private theorem pow_aux (hf : ∀ x, p (f x) ↔ p x) : ∀ {n : ℕ} (x), p ((f ^ n) x) ↔ p x
  | 0, _ => Iff.rfl
  | _ + 1, _ => (pow_aux hf (f _)).trans (hf _)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem subtypePerm_pow (f : Equiv.Perm α) (n : ℕ) (hf) :
    (f.subtypePerm hf : Equiv.Perm { x // p x }) ^ n = (f ^ n).subtypePerm (pow_aux hf) := by
  induction n with
  | zero => simp
  | succ n ih => simp_rw [pow_succ', ih, Equiv.Perm.subtypePerm_mul]

