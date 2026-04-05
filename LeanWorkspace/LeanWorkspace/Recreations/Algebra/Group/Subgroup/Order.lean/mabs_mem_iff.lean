import Mathlib

theorem mabs_mem_iff {S G} [Group G] [LinearOrder G] {_ : SetLike S G}
    [InvMemClass S G] {H : S} {x : G} : |x|ₘ ∈ H ↔ x ∈ H := by
  cases mabs_choice x <;> simp [*]

