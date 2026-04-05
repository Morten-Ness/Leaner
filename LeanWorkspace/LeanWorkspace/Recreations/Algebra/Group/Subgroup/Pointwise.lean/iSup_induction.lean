import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem iSup_induction {ι : Sort*} (S : ι → Subgroup G) {C : G → Prop} {x : G} (hx : x ∈ ⨆ i, S i)
    (mem : ∀ (i), ∀ x ∈ S i, C x) (one : C 1) (mul : ∀ x y, C x → C y → C (x * y)) : C x := by
  rw [iSup_eq_closure] at hx
  induction hx using Subgroup.closure_induction'' with
  | one => exact one
  | mem x hx =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact mem _ _ hi
  | inv_mem x hx =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact mem _ _ (inv_mem hi)
  | mul x y _ _ ihx ihy => exact mul x y ihx ihy

