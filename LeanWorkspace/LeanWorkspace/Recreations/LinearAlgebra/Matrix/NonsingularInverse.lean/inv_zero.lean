import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

set_option backward.isDefEq.respectTransparency false in
theorem inv_zero : (0 : Matrix n n α)⁻¹ = 0 := by
  rcases subsingleton_or_nontrivial α with ht | ht
  · simp [eq_iff_true_of_subsingleton]
  rcases (Fintype.card n).zero_le.eq_or_lt with hc | hc
  · rw [eq_comm, Fintype.card_eq_zero_iff] at hc
    subsingleton
  · have hn : Nonempty n := Fintype.card_pos_iff.mp hc
    refine Matrix.nonsing_inv_apply_not_isUnit _ ?_
    simp [det]

noncomputable instance : InvOneClass (Matrix n n α) :=
  { Matrix.one, Matrix.inv with inv_one := Matrix.inv_eq_left_inv (by simp) }

