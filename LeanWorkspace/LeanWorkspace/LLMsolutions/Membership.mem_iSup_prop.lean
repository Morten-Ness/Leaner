import Mathlib

variable {M A B : Type*}

variable [MulOneClass M]

theorem mem_iSup_prop {p : Prop} {S : p → Submonoid M} {x : M} :
    x ∈ ⨆ (h : p), S h ↔ x = 1 ∨ ∃ (h : p), x ∈ S h := by
  by_cases hp : p
  · let h0 : p := hp
    have hEq : (⨆ (h : p), S h) = S h0 := by
      apply le_antisymm
      · refine iSup_le ?_
        intro h
        cases Subsingleton.elim h h0
        exact le_rfl
      · exact le_iSup (fun h : p => S h) h0
    rw [hEq]
    constructor
    · intro hx
      right
      exact ⟨h0, hx⟩
    · rintro (rfl | ⟨h, hh⟩)
      · exact (S h0).one_mem
      · cases Subsingleton.elim h h0
        simpa using hh
  · have hp' : IsEmpty p := ⟨hp⟩
    have hEq : (⨆ (h : p), S h) = ⊥ := by
      exact iSup_of_empty S
    rw [hEq]
    constructor
    · intro hx
      left
      simpa using hx
    · rintro (rfl | ⟨h, _⟩)
      · simp
      · exact (hp h).elim
