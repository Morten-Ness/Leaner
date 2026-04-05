import Mathlib

section

variable {u v : ℤ}

theorem eq_of_mul_eq_one (h : u * v = 1) : u = v := (Int.eq_one_or_neg_one_of_mul_eq_one' h).elim
    (and_imp.2 (·.trans ·.symm)) (and_imp.2 (·.trans ·.symm))

end

section

variable {u v : ℤ}

theorem eq_one_or_neg_one_of_mul_eq_neg_one' (h : u * v = -1) : u = 1 ∧ v = -1 ∨ u = -1 ∧ v = 1 := by
  obtain rfl | rfl := Int.isUnit_eq_one_or (IsUnit.mul_iff.mp (Int.isUnit_iff.mpr (Or.inr h))).1
  · exact Or.inl ⟨rfl, one_mul v ▸ h⟩
  · simpa [Int.neg_mul] using h

end

section

variable {u v : ℤ}

theorem eq_one_or_neg_one_of_mul_eq_neg_one (h : u * v = -1) : u = 1 ∨ u = -1 := Or.elim (Int.eq_one_or_neg_one_of_mul_eq_neg_one' h) (fun H => Or.inl H.1) fun H => Or.inr H.1

end

section

variable {u v : ℤ}

theorem eq_one_or_neg_one_of_mul_eq_one' (h : u * v = 1) : u = 1 ∧ v = 1 ∨ u = -1 ∧ v = -1 := by
  have h' : v * u = 1 := mul_comm u v ▸ h
  obtain rfl | rfl := Int.eq_one_or_neg_one_of_mul_eq_one h <;>
      obtain rfl | rfl := Int.eq_one_or_neg_one_of_mul_eq_one h' <;> tauto

end

section

variable {u v : ℤ}

theorem eq_one_or_neg_one_of_mul_eq_one (h : u * v = 1) : u = 1 ∨ u = -1 := Int.isUnit_iff.1 (.of_mul_eq_one v h)

end

section

variable {u v : ℤ}

theorem isUnit_add_isUnit_eq_isUnit_add_isUnit {a b c d : ℤ} (ha : IsUnit a) (hb : IsUnit b)
    (hc : IsUnit c) (hd : IsUnit d) : a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c := by
  rw [Int.isUnit_iff] at ha hb hc hd
  lia

end

section

variable {u v : ℤ}

theorem isUnit_eq_or_eq_neg (hu : IsUnit u) (hv : IsUnit v) : u = v ∨ u = -v := or_iff_not_imp_left.2 (Int.isUnit_ne_iff_eq_neg hu hv).1

end

section

variable {u v : ℤ}

theorem isUnit_iff : IsUnit u ↔ u = 1 ∨ u = -1 := by
  refine ⟨fun h ↦ Int.isUnit_eq_one_or h, fun h ↦ ?_⟩
  rcases h with (rfl | rfl)
  · exact isUnit_one
  · exact ⟨⟨-1, -1, by decide, by decide⟩, rfl⟩

end

section

variable {u v : ℤ}

theorem isUnit_mul_self (hu : IsUnit u) : u * u = 1 := (Int.isUnit_eq_one_or hu).elim (fun h ↦ h.symm ▸ rfl) fun h ↦ h.symm ▸ rfl

end

section

variable {u v : ℤ}

theorem isUnit_ne_iff_eq_neg (hu : IsUnit u) (hv : IsUnit v) : u ≠ v ↔ u = -v := by
  obtain rfl | rfl := Int.isUnit_eq_one_or hu <;> obtain rfl | rfl := Int.isUnit_eq_one_or hv <;> decide

end

section

variable {u v : ℤ}

theorem mul_eq_neg_one_iff_eq_one_or_neg_one : u * v = -1 ↔ u = 1 ∧ v = -1 ∨ u = -1 ∧ v = 1 := by
  refine ⟨Int.eq_one_or_neg_one_of_mul_eq_neg_one', fun h ↦ Or.elim h (fun H ↦ ?_) fun H ↦ ?_⟩ <;>
    obtain ⟨rfl, rfl⟩ := H <;> rfl

end

section

variable {u v : ℤ}

theorem mul_eq_one_iff_eq_one_or_neg_one : u * v = 1 ↔ u = 1 ∧ v = 1 ∨ u = -1 ∧ v = -1 := by
  refine ⟨Int.eq_one_or_neg_one_of_mul_eq_one', fun h ↦ Or.elim h (fun H ↦ ?_) fun H ↦ ?_⟩ <;>
    obtain ⟨rfl, rfl⟩ := H <;> rfl

end
