import Mathlib

section

variable {α β γ : Type*}

theorem disjoint_range_addLeftEmbedding (a : ℕ) (s : Finset ℕ) :
    Disjoint (range a) (map (addLeftEmbedding a) s) := by
  simp_rw [disjoint_left, mem_map, mem_range, addLeftEmbedding_apply]
  rintro _ h ⟨l, -, rfl⟩
  lia

end

section

variable {α β γ : Type*}

theorem disjoint_range_addRightEmbedding (a : ℕ) (s : Finset ℕ) :
    Disjoint (range a) (map (addRightEmbedding a) s) := by
  rw [← addLeftEmbedding_eq_addRightEmbedding]
  apply Finset.disjoint_range_addLeftEmbedding

end

section

variable {α β γ : Type*}

theorem range_add (a b : ℕ) : range (a + b) = range a ∪ (range b).map (addLeftEmbedding a) := by
  rw [← val_inj, union_val]
  exact Multiset.range_add_eq_union a b

end
