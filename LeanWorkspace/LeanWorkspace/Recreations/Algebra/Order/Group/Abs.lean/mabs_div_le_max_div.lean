import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem mabs_div_le_max_div {a b c : G} (hac : a ≤ b) (hcd : b ≤ c) (d : G) :
    |b / d|ₘ ≤ max (c / d) (d / a) := by
  rcases le_total d b with h | h
  · rw [mabs_of_one_le <| one_le_div'.mpr h]
    exact le_max_of_le_left <| div_le_div_right' hcd _
  · rw [mabs_of_le_one <| div_le_one'.mpr h, inv_div]
    exact le_max_of_le_right <| div_le_div_left' hac _

