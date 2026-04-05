import Mathlib

variable {ι μ μ' : Type*}

variable [DecidableEq ι] [AddCancelCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {i : ι}
  {s : Finset ι}

theorem piAntidiag_cons (hi : i ∉ s) (n : μ) :
    Finset.piAntidiag (cons i s hi) n = (antidiagonal n).disjiUnion (fun p : μ × μ ↦
      (Finset.piAntidiag s p.snd).map (addRightEmbedding fun t ↦ if t = i then p.fst else 0))
        (Finset.pairwiseDisjoint_piAntidiag_map_addRightEmbedding hi _) := by
  ext f
  simp only [mem_piAntidiag, sum_cons, ne_eq, mem_cons, mem_disjiUnion, mem_antidiagonal, mem_map,
    Prod.exists]
  constructor
  · rintro ⟨hn, hf⟩
    refine ⟨_, _, hn, Function.update f i 0, ⟨sum_update_of_notMem hi _ _, fun j ↦ ?_⟩, by aesop⟩
    have := fun h₁ h₂ ↦ (hf j h₁).resolve_left h₂
    aesop (add simp [Function.update])
  · rintro ⟨a, _, hn, g, ⟨rfl, hg⟩, rfl⟩
    have := hg i
    aesop (add simp [sum_add_distrib])

