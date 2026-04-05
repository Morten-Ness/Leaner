import Mathlib

section

variable {X : Type*}

theorem mem_support_iff (x : X) (a : FreeAbelianGroup X) : x ∈ a.support ↔ FreeAbelianGroup.coeff x a ≠ 0 := by
  rw [FreeAbelianGroup.support, Finsupp.mem_support_iff]
  exact Iff.rfl

end

section

variable {X : Type*}

theorem notMem_support_iff (x : X) (a : FreeAbelianGroup X) : x ∉ a.support ↔ FreeAbelianGroup.coeff x a = 0 := by
  rw [FreeAbelianGroup.support, Finsupp.notMem_support_iff]
  exact Iff.rfl

end

section

open scoped Classical

variable {X : Type*}

theorem support_add (a b : FreeAbelianGroup X) : FreeAbelianGroup.support (a + b) ⊆ a.support ∪ b.support := by
  simp only [FreeAbelianGroup.support, map_add]
  apply Finsupp.support_add

end

section

variable {X : Type*}

theorem support_neg (a : FreeAbelianGroup X) : FreeAbelianGroup.support (-a) = FreeAbelianGroup.support a := by
  simp only [FreeAbelianGroup.support, map_neg, Finsupp.support_neg]

end

section

variable {X : Type*}

theorem support_nsmul (k : ℕ) (h : k ≠ 0) (a : FreeAbelianGroup X) :
    FreeAbelianGroup.support (k • a) = FreeAbelianGroup.support a := by
  apply FreeAbelianGroup.support_zsmul k _ a
  exact mod_cast h

end

section

variable {X : Type*}

theorem support_zero : FreeAbelianGroup.support (0 : FreeAbelianGroup X) = ∅ := by
  simp only [FreeAbelianGroup.support, Finsupp.support_zero, map_zero]

end
