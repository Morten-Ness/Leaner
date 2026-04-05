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

theorem ofSubtype_subtypePerm {f : Equiv.Perm α} (h₁ : ∀ x, p (f x) ↔ p x) (h₂ : ∀ x, f x ≠ x → p x) :
    Equiv.Perm.ofSubtype (Equiv.Perm.subtypePerm f h₁) = f := Equiv.ext fun x => by
    by_cases hx : p x
    · exact (Equiv.Perm.subtypePerm f h₁).extendDomain_apply_subtype _ hx
    · rw [Equiv.Perm.ofSubtype, MonoidHom.coe_mk, OneHom.coe_mk,
        Equiv.Perm.extendDomain_apply_not_subtype _ _ hx]
      exact not_not.mp fun h => hx (h₂ x (Ne.symm h))

