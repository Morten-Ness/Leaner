FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

theorem centroid_eq_of_range_eq {n : ℕ} {s₁ s₂ : Affine.Simplex k P n}
    (h : Set.range s₁.points = Set.range s₂.points) :
    Finset.univ.centroid k s₁.points = Finset.univ.centroid k s₂.points := by
  classical
  let e : Fin (n + 1) ≃ Fin (n + 1) :=
    Equiv.ofBijective
      (fun i =>
        Classical.choose
          (show ∃ j : Fin (n + 1), s₂.points j = s₁.points i by
            have hi : s₁.points i ∈ Set.range s₁.points := ⟨i, rfl⟩
            rw [h] at hi
            simpa [Set.mem_range] using hi))
      (by
        constructor
        · intro i₁ i₂ he
          by_contra hne
          have hpts : s₁.points i₁ = s₁.points i₂ := by
            calc
              s₁.points i₁ = s₂.points (Classical.choose
                  (show ∃ j : Fin (n + 1), s₂.points j = s₁.points i₁ by
                    have hi : s₁.points i₁ ∈ Set.range s₁.points := ⟨i₁, rfl⟩
                    rw [h] at hi
                    simpa [Set.mem_range] using hi)) := by
                      symm
                      exact Classical.choose_spec
                        (show ∃ j : Fin (n + 1), s₂.points j = s₁.points i₁ by
                          have hi : s₁.points i₁ ∈ Set.range s₁.points := ⟨i₁, rfl⟩
                          rw [h] at hi
                          simpa [Set.mem_range] using hi)
              _ = s₂.points (Classical.choose
                  (show ∃ j : Fin (n + 1), s₂.points j = s₁.points i₂ by
                    have hi : s₁.points i₂ ∈ Set.range s₁.points := ⟨i₂, rfl⟩
                    rw [h] at hi
                    simpa [Set.mem_range] using hi)) := by simpa [e] using he
              _ = s₁.points i₂ := by
                    exact Classical.choose_spec
                      (show ∃ j : Fin (n + 1), s₂.points j = s₁.points i₂ by
                        have hi : s₁.points i₂ ∈ Set.range s₁.points := ⟨i₂, rfl⟩
                        rw [h] at hi
                        simpa [Set.mem_range] using hi)
          exact hne (s₁.injective hpts)
        · intro j
          have hj : s₂.points j ∈ Set.range s₂.points := ⟨j, rfl⟩
          rw [← h] at hj
          rcases hj with ⟨i, hi⟩
          refine ⟨i, ?_⟩
          apply s₂.injective
          simpa [e] using (Classical.choose_spec
            (show ∃ j' : Fin (n + 1), s₂.points j' = s₁.points i by ⟨j, hi.symm⟩)) )
  have hcomp : s₁.points = s₂.points ∘ e := by
    funext i
    symm
    exact Classical.choose_spec
      (show ∃ j : Fin (n + 1), s₂.points j = s₁.points i by
        have hi : s₁.points i ∈ Set.range s₁.points := ⟨i, rfl⟩
        rw [h] at hi
        simpa [Set.mem_range] using hi)
  rw [hcomp, Finset.centroid_map_equiv]
