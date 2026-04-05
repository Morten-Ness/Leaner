import Mathlib

variable {A M G α β γ : Type*}

variable {p : α → Prop} {f : Perm α}

variable [DecidablePred p] {a : α}

set_option backward.privateInPublic true in
private theorem inv_aux : (∀ x, p (f x) ↔ p x) ↔ ∀ x, p (f⁻¹ x) ↔ p x := f⁻¹.surjective.forall.trans <| by simp [Iff.comm]


set_option backward.privateInPublic true in
private theorem pow_aux (hf : ∀ x, p (f x) ↔ p x) : ∀ {n : ℕ} (x), p ((f ^ n) x) ↔ p x
  | 0, _ => Iff.rfl
  | _ + 1, _ => (pow_aux hf (f _)).trans (hf _)

set_option backward.privateInPublic true in
private theorem zpow_aux (hf : ∀ x, p (f x) ↔ p x) : ∀ {n : ℤ} (x), p ((f ^ n) x) ↔ p x
  | Int.ofNat _ => pow_aux hf
  | Int.negSucc n => by
    rw [zpow_negSucc]
    exact pow_aux (inv_aux.1 hf)

theorem ofSubtype_apply_mem_iff_mem (f : Equiv.Perm (Subtype p)) (x : α) :
    p ((Equiv.Perm.ofSubtype f : α → α) x) ↔ p x := if h : p x then by
    simpa only [h, iff_true, MonoidHom.coe_mk, Equiv.Perm.ofSubtype_apply_of_mem f h] using (f ⟨x, h⟩).2
  else by simp [h, Equiv.Perm.ofSubtype_apply_of_not_mem f h]

