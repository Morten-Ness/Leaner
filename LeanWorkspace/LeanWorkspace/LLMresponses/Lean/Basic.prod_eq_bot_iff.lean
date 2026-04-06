import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem prod_eq_bot_iff {H : Subgroup G} {K : Subgroup N} : H.prod K = ⊥ ↔ H = ⊥ ∧ K = ⊥ := by
  constructor
  · intro h
    constructor
    · ext x
      constructor
      · intro hx
        have hmem : (x, (1 : N)) ∈ H.prod K := ⟨hx, K.one_mem⟩
        have : (x, (1 : N)) ∈ (⊥ : Subgroup (G × N)) := by simpa [h] using hmem
        simpa [Subgroup.mem_bot] using this
      · intro hx
        rw [Subgroup.mem_bot] at hx
        simpa [hx]
    · ext y
      constructor
      · intro hy
        have hmem : ((1 : G), y) ∈ H.prod K := ⟨H.one_mem, hy⟩
        have : ((1 : G), y) ∈ (⊥ : Subgroup (G × N)) := by simpa [h] using hmem
        simpa [Subgroup.mem_bot] using this
      · intro hy
        rw [Subgroup.mem_bot] at hy
        simpa [hy]
  · rintro ⟨hH, hK⟩
    ext x
    rcases x with ⟨g, n⟩
    simp [hH, hK, Subgroup.mem_bot]
