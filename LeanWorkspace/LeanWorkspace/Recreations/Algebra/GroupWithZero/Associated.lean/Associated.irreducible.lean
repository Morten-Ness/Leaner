import Mathlib

variable {M : Type*}

theorem Associated.irreducible [Monoid M] {p q : M} (h : p ~ᵤ q) (hp : Irreducible p) :
    Irreducible q := ⟨mt Associated.symm h.isUnit hp.1,
    let ⟨u, hu⟩ := h
    fun a b hab =>
    have hpab : p = a * (b * (u⁻¹ : Mˣ)) :=
      calc
        p = p * u * (u⁻¹ : Mˣ) := by simp
        _ = _ := by rw [hu]; simp [hab, mul_assoc]
    (hp.isUnit_or_isUnit hpab).elim Or.inl fun ⟨v, hv⟩ => Or.inr ⟨v * u, by simp [hv]⟩⟩

