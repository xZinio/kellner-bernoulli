import KellnerBernoulli

/-! Run with `lake env lean scripts/Axioms.lean`.  Every result should depend only on
`propext`, `Classical.choice` and `Quot.sound` (no `sorryAx`, no `Lean.ofReduceBool`). -/

#print axioms KellnerBernoulli.kellner_conjecture
#print axioms KellnerBernoulli.kellner_conjecture_of_lt
#print axioms KellnerBernoulli.kellner_exceptions
#print axioms KellnerBernoulli.bernoulli_derivative_intCoeffs_iff
#print axioms KellnerBernoulli.bernoulli_derivative_mem_lifts_iff
#print axioms KellnerBernoulli.bernoulli_iterate_derivative_two
#print axioms KellnerBernoulli.bernoulli_iterate_derivative_three
#print axioms KellnerBernoulli.oeis_A195441
#print axioms KellnerBernoulli.kellner2017
#print axioms KellnerBernoulli.alekseyev
#print axioms KellnerBernoulli.ThetaBound.of_rosserSchoenfeld
#print axioms KellnerBernoulli.ThetaBound.of_dusart
