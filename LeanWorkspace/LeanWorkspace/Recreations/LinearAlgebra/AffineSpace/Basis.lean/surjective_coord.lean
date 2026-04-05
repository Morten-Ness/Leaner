import Mathlib

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

theorem surjective_coord [Nontrivial ι] (i : ι) : Function.Surjective <| b.coord i := by
  classical
    intro x
    obtain ⟨j, hij⟩ := exists_ne i
    let s : Finset ι := {i, j}
    have hi : i ∈ s := by simp [s]
    let w : ι → k := fun j' => if j' = i then x else 1 - x
    have hw : s.sum w = 1 := by simp [s, w, Finset.sum_ite, Finset.filter_insert, hij,
      Finset.filter_true_of_mem, Finset.filter_false_of_mem]
    use s.affineCombination k b w
    simp [w, AffineBasis.coord_apply_combination_of_mem b hi hw]

