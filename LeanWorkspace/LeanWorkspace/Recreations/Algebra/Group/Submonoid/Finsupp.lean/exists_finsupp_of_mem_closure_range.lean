import Mathlib

variable {M : Type*} [CommMonoid M] {ι : Type*} (f : ι → M) (x : M)

theorem exists_finsupp_of_mem_closure_range (hx : x ∈ closure (Set.range f)) :
    ∃ a : ι →₀ ℕ, x = a.prod (f · ^ ·) := by
  classical
  induction hx using closure_induction with
  | mem x h => obtain ⟨i, rfl⟩ := h; exact ⟨Finsupp.single i 1, by simp⟩
  | one => use 0; simp
  | mul x y hx hy hx' hy' =>
    obtain ⟨⟨v, rfl⟩, w, rfl⟩ := And.intro hx' hy'
    use v + w
    rw [Finsupp.prod_add_index]
    · simp
    · simp [pow_add]

