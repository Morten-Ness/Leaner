FAIL
import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable {s : Subfield K}

theorem map_field_closure (f : K →+* L) (s : Set K) : (Subfield.closure s).map f = Subfield.closure (f '' s) := by
  ext y
  constructor
  · intro hy
    refine Subfield.closure_le.2 ?_
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact ⟨x, Subfield.subset_closure hx, rfl⟩
  · intro hy
    refine Subfield.closure_induction hy ?_ ?_ ?_ ?_ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, Subfield.subset_closure hx, rfl⟩
    · exact ⟨1, Subfield.one_mem _, map_one f⟩
    · intro a b ha hb
      rcases ha with ⟨a', ha', rfl⟩
      rcases hb with ⟨b', hb', rfl⟩
      exact ⟨a' + b', Subfield.add_mem _ ha' hb', map_add f a' b'⟩
    · intro a b ha hb
      rcases ha with ⟨a', ha', rfl⟩
      rcases hb with ⟨b', hb', rfl⟩
      exact ⟨a' * b', Subfield.mul_mem _ ha' hb', map_mul f a' b'⟩
    · intro a ha
      rcases ha with ⟨a', ha', rfl⟩
      exact ⟨-a', Subfield.neg_mem _ ha', map_neg f a'⟩
    · intro a ha
      rcases ha with ⟨a', ha', rfl⟩
      exact ⟨a'⁻¹, Subfield.inv_mem _ ha', map_inv₀ f a'⟩
