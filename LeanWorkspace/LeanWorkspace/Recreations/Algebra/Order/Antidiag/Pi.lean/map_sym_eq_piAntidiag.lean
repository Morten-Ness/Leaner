import Mathlib

variable {ι μ μ' : Type*}

theorem map_sym_eq_piAntidiag [DecidableEq ι] (s : Finset ι) (n : ℕ) :
    (s.sym n).map ⟨fun m a ↦ m.1.count a, Multiset.count_injective.comp Sym.coe_injective⟩ =
      Finset.piAntidiag s n := by
  ext f
  simp only [Sym.val_eq_coe, mem_map, mem_sym_iff, Embedding.coeFn_mk, funext_iff, Sym.exists,
    Sym.mem_mk, Sym.coe_mk, exists_and_left, exists_prop, mem_piAntidiag, ne_eq]
  constructor
  · rintro ⟨m, hm, rfl, hf⟩
    simpa [← hf, Multiset.sum_count_eq_card hm]
  · rintro ⟨rfl, hf⟩
    refine ⟨∑ a ∈ s, f a • {a}, ?_, ?_⟩
    · simp +contextual
    · simpa [Multiset.count_sum', Multiset.count_singleton, not_imp_comm, eq_comm (a := 0)] using hf

