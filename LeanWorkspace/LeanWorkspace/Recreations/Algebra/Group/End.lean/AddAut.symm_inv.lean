import Mathlib

variable {A M G α β γ : Type*}

variable (A) [Add A]

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

theorem symm_inv (e : AddAut A) : e.symm⁻¹ = e := rfl

