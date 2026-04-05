import Mathlib

variable {ι R S : Type*}

variable [CommMonoidWithZero R]

variable [PartialOrder R] [ZeroLEOneClass R] [PosMulStrictMono R] [Nontrivial R] {f g : ι → R}
  {s t : Finset ι}

theorem prod_lt_prod (hf : ∀ i ∈ s, 0 < f i) (hfg : ∀ i ∈ s, f i ≤ g i)
    (hlt : ∃ i ∈ s, f i < g i) :
    ∏ i ∈ s, f i < ∏ i ∈ s, g i := by
  classical
  obtain ⟨i, hi, hilt⟩ := hlt
  rw [← insert_erase hi, prod_insert (notMem_erase _ _), prod_insert (notMem_erase _ _)]
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹PosMulStrictMono R›
  refine mul_lt_mul_of_pos_of_nonneg' hilt ?_ ?_ ?_
  · exact Finset.prod_le_prod (fun j hj => le_of_lt (hf j (mem_of_mem_erase hj)))
      (fun _ hj ↦ hfg _ <| mem_of_mem_erase hj)
  · exact Finset.prod_pos fun j hj => hf j (mem_of_mem_erase hj)
  · exact (hf i hi).le.trans hilt.le

