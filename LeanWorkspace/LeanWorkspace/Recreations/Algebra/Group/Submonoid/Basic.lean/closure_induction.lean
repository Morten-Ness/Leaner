import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem closure_induction {s : Set M} {motive : (x : M) → x ∈ Submonoid.closure s → Prop}
    (mem : ∀ (x) (h : x ∈ s), motive x (Submonoid.subset_closure h)) (one : motive 1 (one_mem _))
    (mul : ∀ x y hx hy, motive x hx → motive y hy → motive (x * y) (mul_mem hx hy)) {x}
    (hx : x ∈ Submonoid.closure s) : motive x hx := let S : Submonoid M :=
    { carrier := { x | ∃ hx, motive x hx }
      one_mem' := ⟨_, one⟩
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, mul _ _ _ _ hpx hpy⟩ }
  Submonoid.closure_le (S := S) |>.mpr (fun y hy ↦ ⟨Submonoid.subset_closure hy, mem y hy⟩) hx |>.elim fun _ ↦ id

