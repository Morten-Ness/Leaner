import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem mem_closure_iff {s : Set R} {x} :
    x ∈ Subring.closure s ↔ x ∈ AddSubgroup.closure (Submonoid.closure s : Set R) := ⟨fun h => by
    induction h using Subring.closure_induction with
    | mem _ hx => exact AddSubgroup.subset_closure (Submonoid.subset_closure hx)
    | zero => exact zero_mem _
    | one => exact AddSubgroup.subset_closure (one_mem _)
    | add _ _ _ _ hx hy => exact add_mem hx hy
    | neg _ _ hx => exact neg_mem hx
    | mul _ _ _hx _hy hx hy =>
      clear _hx _hy
      induction hx, hy using AddSubgroup.closure_induction₂ with
      | mem _ _ hx hy => exact AddSubgroup.subset_closure (mul_mem hx hy)
      | zero_left => simp
      | zero_right => simp
      | add_left _ _ _ _ _ _ h₁ h₂ => simpa [add_mul] using add_mem h₁ h₂
      | add_right _ _ _ _ _ _ h₁ h₂ => simpa [mul_add] using add_mem h₁ h₂
      | neg_left _ _ _ _ h => simpa [neg_mul] using neg_mem h
      | neg_right _ _ _ _ h => simpa [mul_neg] using neg_mem h,
    fun h => by
      induction h using AddSubgroup.closure_induction with
      | mem x hx =>
        induction hx using Submonoid.closure_induction with
        | mem _ h => exact Subring.subset_closure h
        | one => exact one_mem _
        | mul _ _ _ _ h₁ h₂ => exact mul_mem h₁ h₂
      | zero => exact zero_mem _
      | add _ _ _ _ h₁ h₂ => exact add_mem h₁ h₂
      | neg _ _ h => exact neg_mem h⟩

