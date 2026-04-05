import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

variable (f : K →+* L)

theorem map_mem_map (f : K →+* L) {s : Subfield K} {x : K} : f x ∈ s.map f ↔ x ∈ s := calc
    _ ↔ f x ∈ (s.map f : Set L) := Iff.rfl
    _ ↔ _ := by simp [Function.Injective.mem_set_image (f := f) f.injective]

