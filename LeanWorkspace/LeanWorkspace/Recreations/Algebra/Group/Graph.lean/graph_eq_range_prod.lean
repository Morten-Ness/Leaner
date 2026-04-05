import Mathlib

variable {G H I : Type*}

variable [Group G] [Group H] [Group I]

theorem graph_eq_range_prod (f : G →* H) : f.graph = Set.range ((id _).prod f) := by aesop

