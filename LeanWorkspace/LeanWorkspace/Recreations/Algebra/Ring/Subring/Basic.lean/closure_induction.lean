import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem closure_induction {s : Set R} {p : (x : R) → x ∈ Subring.closure s → Prop}
    (mem : ∀ (x) (hx : x ∈ s), p x (Subring.subset_closure hx))
    (zero : p 0 (zero_mem _)) (one : p 1 (one_mem _))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (neg : ∀ x hx, p x hx → p (-x) (neg_mem hx))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    {x} (hx : x ∈ Subring.closure s) : p x hx := let K : Subring R :=
    { carrier := { x | ∃ hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, add _ _ _ _ hpx hpy⟩
      neg_mem' := fun ⟨_, hpx⟩ ↦ ⟨_, neg _ _ hpx⟩
      zero_mem' := ⟨_, zero⟩
      one_mem' := ⟨_, one⟩ }
  Subring.closure_le (t := K) |>.mpr (fun y hy ↦ ⟨Subring.subset_closure hy, mem y hy⟩) hx |>.elim fun _ ↦ id

