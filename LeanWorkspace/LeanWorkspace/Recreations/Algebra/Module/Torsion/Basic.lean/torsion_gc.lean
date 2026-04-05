import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem torsion_gc :
    @GaloisConnection (Submodule R M) (Ideal R)ᵒᵈ _ _ annihilator fun I =>
      Submodule.torsionBySet R M ↑(OrderDual.ofDual I) := fun _ _ =>
  ⟨fun h x hx => (Submodule.mem_torsionBySet_iff _ _).mpr fun ⟨_, ha⟩ => mem_annihilator.mp (h ha) x hx,
    fun h a ha => mem_annihilator.mpr fun _ hx => (Submodule.mem_torsionBySet_iff _ _).mp (h hx) ⟨a, ha⟩⟩

