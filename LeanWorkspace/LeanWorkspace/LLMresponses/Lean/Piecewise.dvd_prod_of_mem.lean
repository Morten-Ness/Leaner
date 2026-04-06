import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem dvd_prod_of_mem (f : ι → M) {a : ι} {s : Finset ι} (ha : a ∈ s) : f a ∣ ∏ i ∈ s, f i := by
  classical
  refine Finset.induction_on s ?h ?step ha
  · intro h
    cases h
  · intro b t hb ht ha
    rw [Finset.mem_insert] at ha
    rcases ha with rfl | ha'
    · refine ⟨∏ x ∈ t, f x, by simp [hb]⟩
    · rcases ht ha' with ⟨c, hc⟩
      refine ⟨f b * c, by simp [Finset.prod_insert, hb, hc, mul_assoc, mul_left_comm, mul_comm]⟩
