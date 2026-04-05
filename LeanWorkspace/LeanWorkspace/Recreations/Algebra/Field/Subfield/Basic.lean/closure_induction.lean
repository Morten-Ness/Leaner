import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem closure_induction {s : Set K} {p : ∀ x ∈ Subfield.closure s, Prop}
    (mem : ∀ x hx, p x (Subfield.subset_closure hx))
    (one : p 1 (one_mem _)) (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (neg : ∀ x hx, p x hx → p (-x) (neg_mem hx)) (inv : ∀ x hx, p x hx → p x⁻¹ (inv_mem hx))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    {x} (h : x ∈ Subfield.closure s) : p x h := letI : Subfield K :=
    { carrier := {x | ∃ hx, p x hx}
      mul_mem' := by rintro _ _ ⟨_, hx⟩ ⟨_, hy⟩; exact ⟨_, mul _ _ _ _ hx hy⟩
      one_mem' := ⟨_, one⟩
      add_mem' := by rintro _ _ ⟨_, hx⟩ ⟨_, hy⟩; exact ⟨_, add _ _ _ _ hx hy⟩
      zero_mem' := ⟨zero_mem _, by
        simp_rw [← @add_neg_cancel K _ 1]; exact add _ _ _ _ one (neg _ _ one)⟩
      neg_mem' := by rintro _ ⟨_, hx⟩; exact ⟨_, neg _ _ hx⟩
      inv_mem' := by rintro _ ⟨_, hx⟩; exact ⟨_, inv _ _ hx⟩ }
  ((Subfield.closure_le (t := this)).2 (fun x hx ↦ ⟨_, mem x hx⟩) h).2

