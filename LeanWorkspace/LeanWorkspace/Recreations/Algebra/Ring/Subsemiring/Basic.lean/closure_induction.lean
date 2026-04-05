import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem closure_induction {s : Set R} {p : (x : R) → x ∈ Subsemiring.closure s → Prop}
    (mem : ∀ (x) (hx : x ∈ s), p x (Subsemiring.subset_closure hx))
    (zero : p 0 (zero_mem _)) (one : p 1 (one_mem _))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    {x} (hx : x ∈ Subsemiring.closure s) : p x hx := let K : Subsemiring R :=
    { carrier := { x | ∃ hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, add _ _ _ _ hpx hpy⟩
      one_mem' := ⟨_, one⟩
      zero_mem' := ⟨_, zero⟩ }
  Subsemiring.closure_le (t := K) |>.mpr (fun y hy ↦ ⟨Subsemiring.subset_closure hy, mem y hy⟩) hx |>.elim fun _ ↦ id

