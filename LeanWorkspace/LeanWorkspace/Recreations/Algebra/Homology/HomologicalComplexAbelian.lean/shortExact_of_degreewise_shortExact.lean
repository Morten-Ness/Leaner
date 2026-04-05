import Mathlib

variable {C ι : Type*} {c : ComplexShape ι} [Category* C]

variable [Abelian C]

variable (S : ShortComplex (HomologicalComplex C c))

theorem shortExact_of_degreewise_shortExact
    (hS : ∀ (i : ι), (S.map (eval C c i)).ShortExact) :
    S.ShortExact where
  mono_f := mono_of_mono_f _ (fun i => (hS i).mono_f)
  epi_g := epi_of_epi_f _ (fun i => (hS i).epi_g)
  exact := HomologicalComplex.exact_of_degreewise_exact S (fun i => (hS i).exact)

