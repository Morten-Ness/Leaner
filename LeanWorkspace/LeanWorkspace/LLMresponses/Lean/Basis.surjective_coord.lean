FAIL
import Mathlib

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

theorem surjective_coord [Nontrivial ι] (i : ι) : Function.Surjective <| b.coord i := by
  classical
  intro x
  by_cases hx : x = 1
  · refine ⟨b i, ?_⟩
    simp [b.coord_apply, hx]
  · obtain ⟨j, hji'⟩ := exists_ne i
    refine ⟨b j, ?_⟩
    have hji : i ≠ j := fun h => hji' h.symm
    rw [b.coord_apply]
    simp [hji]
    exfalso
    exact hx rfl
