import KellnerBernoulli

/-!
Run with `lake env lean scripts/Axioms.lean` (the CI does this after `lake build`).

The commands below print the axioms used by the main results and **fail** (so that `lean` exits with a
non-zero status) if any of them, or any other declaration of the project, depends on an axiom other than
`propext`, `Classical.choice` and `Quot.sound`; for instance `sorryAx` (from `sorry`) or
`Lean.ofReduceBool` (from `native_decide`).  The hypothesis `ThetaBound` is not an axiom: it is an
explicit assumption of the theorems that use it.
-/

open Lean Elab Command

/-- The axioms that the project may use. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `#assert_axioms c₁ … cₙ` prints the axioms used by each `cᵢ` and fails if one is not allowed. -/
elab "#assert_axioms" ids:(ppSpace colGt ident)+ : command => do
  for id in ids do
    let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← collectAxioms c
    logInfo m!"{c}: {axs.toList}"
    for ax in axs do
      unless allowedAxioms.contains ax do
        throwErrorAt id "{c} depends on the axiom {ax}"

/-- `#assert_axioms_prefix P` checks every declaration whose name begins with `P`. -/
elab "#assert_axioms_prefix" pre:ident : command => do
  let env ← getEnv
  let names := env.constants.fold
    (fun acc c _ => if pre.getId.isPrefixOf c then acc.push c else acc) #[]
  let mut bad : Array MessageData := #[]
  for c in names do
    for ax in (← collectAxioms c) do
      unless allowedAxioms.contains ax do
        bad := bad.push m!"{c} uses {ax}"
  if bad.isEmpty then
    logInfo m!"all {names.size} declarations with prefix {pre.getId} use only {allowedAxioms}"
  else
    throwError m!"axioms not allowed:{indentD (MessageData.joinSep bad.toList Format.line)}"

-- Theorem 1
#assert_axioms KellnerBernoulli.kellner_conjecture KellnerBernoulli.kellner_conjecture_of_lt
  KellnerBernoulli.kellner_exceptions KellnerBernoulli.card_goodPrimes_ge_of_lt
  KellnerBernoulli.card_goodPrimes_ge_of_thetaBound KellnerBernoulli.card_goodPrimes_thresholds
-- Lemmas 7 and 8, Proposition 9
#assert_axioms KellnerBernoulli.bad_imp KellnerBernoulli.div_pred_le KellnerBernoulli.card_bad_mul_lt
  KellnerBernoulli.squarefree_polyDen_bernoulli_sub KellnerBernoulli.prime_dvd_polyDen_bernoulli_sub_iff
  KellnerBernoulli.squarefree_polyDen_iterate_derivative
  KellnerBernoulli.prime_dvd_polyDen_iterate_derivative_iff
  KellnerBernoulli.intCoeffs_iterate_derivative_iff'
-- Corollaries 2-6
#assert_axioms KellnerBernoulli.bernoulli_derivative_intCoeffs_iff
  KellnerBernoulli.bernoulli_derivative_mem_lifts_iff KellnerBernoulli.oeis_A195441
  KellnerBernoulli.bernoulli_sub_den_eq_radical_iff KellnerBernoulli.bernoulli_iterate_derivative_two
  KellnerBernoulli.bernoulli_iterate_derivative_three KellnerBernoulli.kellner2017
  KellnerBernoulli.alekseyev
-- The published estimates imply the hypothesis `ThetaBound`
#assert_axioms KellnerBernoulli.ThetaBound.of_rosserSchoenfeld KellnerBernoulli.ThetaBound.of_dusart
-- Everything else
#assert_axioms_prefix KellnerBernoulli
