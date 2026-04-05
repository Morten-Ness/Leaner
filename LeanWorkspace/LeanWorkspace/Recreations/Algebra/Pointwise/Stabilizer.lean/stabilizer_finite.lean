import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G} {s t : Set α}

variable {s : Set G}

theorem stabilizer_finite (hs₀ : s.Nonempty) (hs : s.Finite) : (stabilizer G s : Set G).Finite := by
  obtain ⟨a, ha⟩ := hs₀
  exact (hs.div <| finite_singleton _).subset <| MulAction.stabilizer_subset_div_right ha

