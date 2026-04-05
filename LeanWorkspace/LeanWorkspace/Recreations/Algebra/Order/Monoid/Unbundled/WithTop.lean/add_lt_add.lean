import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithTop α} {a b : α}

theorem add_lt_add [Preorder α] [AddLeftStrictMono α] [AddRightStrictMono α]
    (xz : x < z) (yw : y < w) : x + y < z + w := by
  apply (WithTop.add_lt_add_left xz.ne_top yw).trans_le
  cases w
  · simp
  · exact (WithTop.add_lt_add_right coe_ne_top xz).le

protected lemma add_le_add_iff_left [LE α] [AddLeftMono α] [AddLeftReflectLE α] (hx : x ≠ ⊤) :
    x + y ≤ x + z ↔ y ≤ z := ⟨WithTop.le_of_add_le_add_left hx, fun _ ↦ by gcongr⟩

protected lemma add_le_add_iff_right [LE α] [AddRightMono α] [AddRightReflectLE α] (hz : z ≠ ⊤) :
    x + z ≤ y + z ↔ x ≤ y := ⟨WithTop.le_of_add_le_add_right hz, fun _ ↦ by gcongr⟩

protected lemma add_lt_add_iff_left [LT α] [AddLeftStrictMono α] [AddLeftReflectLT α] (hx : x ≠ ⊤) :
    x + y < x + z ↔ y < z := ⟨lt_of_add_lt_add_left, WithTop.add_lt_add_left hx⟩

protected lemma add_lt_add_iff_right [LT α] [AddRightStrictMono α] [AddRightReflectLT α]
    (hz : z ≠ ⊤) : x + z < y + z ↔ x < y := ⟨lt_of_add_lt_add_right, WithTop.add_lt_add_right hz⟩

