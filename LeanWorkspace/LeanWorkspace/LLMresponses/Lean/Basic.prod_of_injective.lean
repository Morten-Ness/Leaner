FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable {ι κ ι : Type*} [Fintype ι] [Fintype κ]

variable [CommMonoid M]

theorem prod_of_injective (e : ι → κ) (he : Function.Injective e) (f : ι → M) (g : κ → M)
    (h' : ∀ i ∉ Set.range e, g i = 1) (h : ∀ i, f i = g (e i)) : ∏ i, f i = ∏ j, g j := by
  classical
  rw [show (∏ i, f i) = ∏ i, g (e i) by
    refine Finset.prod_congr rfl ?_
    intro i hi
    exact h i]
  let s : Finset κ := Finset.univ.filter (fun j => j ∈ Set.range e)
  have hs : s = Finset.univ.map ⟨e, he⟩ := by
    ext j
    simp [s]
  let t : Finset κ := Finset.univ.filter (fun j => j ∉ Set.range e)
  have hdisj : Disjoint (Finset.univ.map ⟨e, he⟩) t := by
    refine Finset.disjoint_left.2 ?_
    intro x hx1 hx2
    have hx2' : x ∉ Set.range e := by
      simpa [t] using hx2
    have hx1' : x ∈ Set.range e := by
      rcases (Finset.mem_map.mp hx1) with ⟨i, -, rfl⟩
      exact ⟨i, rfl⟩
    exact hx2' hx1'
  have hunion : (Finset.univ.map ⟨e, he⟩).disjUnion t hdisj = Finset.univ := by
    ext j
    simp [t]
    by_cases hj : j ∈ Set.range e <;> simp [hj, hs]
  have ht : ∏ x ∈ t, g x = 1 := by
    refine Finset.prod_induction ?hbase ?hstep t
    · simp
    · intro a s ha hsdisj ih
      simp only [Finset.prod_insert ha]
      have ha' : a ∉ Set.range e := by
        simpa [t] using Finset.mem_filter.mp (by
          exact Finset.mem_insert_self a s)
      rw [h' a ha', ih, mul_one]
  calc
    ∏ x : ι, g (e x) = ∏ y in Finset.univ.map ⟨e, he⟩, g y := by
      rw [Finset.prod_map]
    _ = (∏ y in (Finset.univ.map ⟨e, he⟩).disjUnion t hdisj, g y) := by
      rw [Finset.prod_disjUnion hdisj, ht, mul_one]
    _ = ∏ y : κ, g y := by
      simpa [hunion]
