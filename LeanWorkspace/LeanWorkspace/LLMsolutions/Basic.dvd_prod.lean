import Mathlib

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem dvd_prod : a ∈ s → a ∣ s.prod := by
  intro ha
  induction s using Multiset.induction_on with
  | empty =>
      cases ha
  | @cons b s ih =>
      simp at ha ⊢
      rcases ha with rfl | hs
      · exact ⟨s.prod, by simp⟩
      · rcases ih hs with ⟨c, hc⟩
        exact ⟨b * c, by simp [hc, mul_assoc, mul_left_comm, mul_comm]⟩
