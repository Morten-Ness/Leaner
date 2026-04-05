import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_induction {p : (g : G) → g ∈ Subgroup.closure k → Prop}
    (mem : ∀ x (hx : x ∈ k), p x (Subgroup.subset_closure hx)) (one : p 1 (one_mem _))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    (inv : ∀ x hx, p x hx → p x⁻¹ (inv_mem hx)) {x} (hx : x ∈ Subgroup.closure k) : p x hx := let K : Subgroup G :=
    { carrier := { x | ∃ hx, p x hx }
      mul_mem' := fun ⟨_, ha⟩ ⟨_, hb⟩ ↦ ⟨_, mul _ _ _ _ ha hb⟩
      one_mem' := ⟨_, one⟩
      inv_mem' := fun ⟨_, hb⟩ ↦ ⟨_, inv _ _ hb⟩ }
  Subgroup.closure_le (K := K) |>.mpr (fun y hy ↦ ⟨Subgroup.subset_closure hy, mem y hy⟩) hx |>.elim fun _ ↦ id

