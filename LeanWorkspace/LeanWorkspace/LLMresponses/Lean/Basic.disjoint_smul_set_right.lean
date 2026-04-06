FAIL
import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem disjoint_smul_set_right : Disjoint s (a • t) ↔ Disjoint (a⁻¹ • s) t := by
  constructor
  · intro h
    rw [Set.disjoint_iff_inter_eq_empty] at h ⊢
    apply Set.eq_empty_iff_forall_not_mem.2
    intro x hx
    have hx1 : x ∈ t := hx.2
    have hx2 : a • x ∈ s := by
      rcases hx.1 with ⟨y, hy, hxy⟩
      simpa [smul_smul, inv_mul_cancel_left] using hxy ▸ hy
    have hx' : a • x ∈ s ∩ (a • t) := by
      constructor
      · exact hx2
      · exact ⟨x, hx1, rfl⟩
    have : a • x ∈ (∅ : Set β) := by simpa [Set.disjoint_iff_inter_eq_empty] using congrArg (fun u => a • x ∈ u) h
    exact this hx'
  · intro h
    rw [Set.disjoint_iff_inter_eq_empty] at h ⊢
    apply Set.eq_empty_iff_forall_not_mem.2
    intro x hx
    have hx1 : x ∈ s := hx.1
    rcases hx.2 with ⟨y, hy, rfl⟩
    have hy' : y ∈ (a⁻¹ • s) ∩ t := by
      constructor
      · exact ⟨x, hx1, by simp⟩
      · exact hy
    have : y ∈ (∅ : Set β) := by simpa [Set.disjoint_iff_inter_eq_empty] using congrArg (fun u => y ∈ u) h
    exact this hy'
