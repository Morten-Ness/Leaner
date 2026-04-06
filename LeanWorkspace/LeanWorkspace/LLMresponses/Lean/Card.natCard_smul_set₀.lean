FAIL
import Mathlib

open scoped Cardinal Pointwise

variable {G₀ M₀ : Type*}

variable [GroupWithZero G₀] [Zero M₀] [MulActionWithZero G₀ M₀] {a : G₀}

theorem natCard_smul_set₀ (ha : a ≠ 0) (s : Set M₀) : Nat.card ↥(a • s) = Nat.card s := by
  classical
  simp_rw [Nat.card_eq_fintype_card]
  classical
  exact Fintype.card_of_bijective
    (fun x : s => ⟨a • x.1, by
      exact ⟨x.1, x.2, rfl⟩⟩)
    (by
      constructor
      · intro x y h
        apply Subtype.ext
        exact smul_eq_smul.mp (Subtype.ext_iff.mp h)
      · intro y
        rcases y.2 with ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩)
