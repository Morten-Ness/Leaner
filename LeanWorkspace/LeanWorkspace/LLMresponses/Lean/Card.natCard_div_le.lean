FAIL
import Mathlib

open scoped Cardinal Pointwise

variable {G M α : Type*}

variable [Group G] {s t : Set G}

theorem natCard_div_le : Nat.card (s / t) ≤ Nat.card s * Nat.card t := by
  classical
  let e : s × t ≃ s / t := by
    classical
    refine
      { toFun := fun p => ⟨p.1.1 / p.2.1, ?_⟩
        invFun := fun x => by
          classical
          by_cases hx : x.1 ∈ s / t
          · rcases hx with ⟨a, ha, b, hb, hab⟩
            exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
          · exact False.elim (hx x.2)
        left_inv := ?_
        right_inv := ?_ }
    · exact ⟨p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩
    · intro p
      rcases p with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      rfl
    · intro x
      rcases x with ⟨x, hx⟩
      rcases hx with ⟨a, ha, b, hb, rfl⟩
      rfl
  have h1 : Nat.card (s / t) ≤ Nat.card (s × t) := by
    simpa using Nat.card_congr e.symm |>.le
  simpa [Nat.card_prod] using h1
