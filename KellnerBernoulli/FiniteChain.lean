import KellnerBernoulli.Finite

/-!
# Kernel computation, part 1: `2015 ≤ n < 10 ^ 8`
-/

namespace KellnerBernoulli

/-- Lower end of the `i`-th segment of the chain. -/
def segLo (i : ℕ) : ℕ := bif Nat.beq i 0 then 2015 else (100 * i) * (100 * i)

/-- The chain in segments `(100 i) ^ 2 ≤ n < (100 (i + 1)) ^ 2`. -/
def chainCheck : Bool :=
  (List.range 100).all (fun i => loop ((100 * (i + 1)) * (100 * (i + 1))) 2000 (segLo i) Data.chain)

theorem trial_incr : incr Data.trial = true := by decide +kernel

theorem chain_isPrime : allR isPrime Data.chain = true := by decide +kernel

theorem chain_incr : incr Data.chain = true := by decide +kernel

theorem chainCheck_true : chainCheck = true := by decide +kernel

/-- Every `n` with `2015 ≤ n < 10 ^ 8` has three good primes. -/
theorem three_good_of_lt {n : ℕ} (h1 : 2015 ≤ n) (h2 : n < 100000000) :
    3 ≤ (goodPrimes n).card := by
  have hpr : ∀ p ∈ Data.chain, p.Prime := fun p hp =>
    prime_of_isPrime (pairwise_of_incr trial_incr) (allR_eq_true.mp chain_isPrime p hp)
  have hpw := pairwise_of_incr chain_incr
  have hall := chainCheck_true
  unfold chainCheck at hall
  rw [List.all_eq_true] at hall
  set s := Nat.sqrt n with hs
  have hs1 : s * s ≤ n := Nat.sqrt_le n
  have hs2 : n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt n
  set i := s / 100 with hi
  have hslt : s < 10000 := by
    by_contra hcon
    have : 10000 ≤ s := by omega
    nlinarith
  have hi100 : i < 100 := by omega
  have hdm : 100 * i ≤ s := by omega
  have hdm2 : s + 1 ≤ 100 * (i + 1) := by omega
  refine loop_sound 2000 (segLo i) Data.chain (hall i (List.mem_range.mpr hi100)) hpw hpr n ?_ ?_
  · unfold segLo
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · rw [h0]; exact h1
    · have : Nat.beq i 0 = false := by
        rcases h : Nat.beq i 0 with _ | _
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) (by omega)
      rw [this, Bool.cond_false]
      exact le_trans (Nat.mul_le_mul hdm hdm) hs1
  · exact lt_of_lt_of_le hs2 (Nat.mul_le_mul hdm2 hdm2)

end KellnerBernoulli
