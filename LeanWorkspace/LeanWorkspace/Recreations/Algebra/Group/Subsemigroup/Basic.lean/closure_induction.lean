import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem closure_induction {p : (x : M) → x ∈ Subsemigroup.closure s → Prop}
    (mem : ∀ (x) (h : x ∈ s), p x (Subsemigroup.subset_closure h))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy)) {x} (hx : x ∈ Subsemigroup.closure s) :
    p x hx := let S : Subsemigroup M :=
    { carrier := { x | ∃ hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, mul _ _ _ _ hpx hpy⟩ }
  Subsemigroup.closure_le (S := S) |>.mpr (fun y hy ↦ ⟨Subsemigroup.subset_closure hy, mem y hy⟩) hx |>.elim fun _ ↦ id

