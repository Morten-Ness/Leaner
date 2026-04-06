import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_induction {p : (g : G) → g ∈ Subgroup.closure k → Prop}
    (mem : ∀ x (hx : x ∈ k), p x (Subgroup.subset_closure hx)) (one : p 1 (one_mem _))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    (inv : ∀ x hx, p x hx → p x⁻¹ (inv_mem hx)) {x} (hx : x ∈ Subgroup.closure k) : p x hx := by
  let S : Subgroup G :=
    { carrier := {x | ∃ hx : x ∈ Subgroup.closure k, p x hx}
      one_mem' := ⟨one_mem _, one⟩
      mul_mem' := by
        intro x y hx hy
        rcases hx with ⟨hx, hpx⟩
        rcases hy with ⟨hy, hpy⟩
        exact ⟨mul_mem hx hy, mul x y hx hy hpx hpy⟩
      inv_mem' := by
        intro x hx
        rcases hx with ⟨hx, hpx⟩
        exact ⟨inv_mem hx, inv x hx hpx⟩ }
  have hk : k ⊆ S := by
    intro x hxk
    exact ⟨Subgroup.subset_closure hxk, mem x hxk⟩
  have hclosure : Subgroup.closure k ≤ S := by
    rw [Subgroup.closure_le]
    exact hk
  exact (hclosure hx).2
