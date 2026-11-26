import KellnerBernoulli.Corollaries

/-!
# Denominators of polynomials (Proposition 9 of the paper, as stated there)

`polyDen P` is the denominator of `P ∈ ℚ[X]`, the least common multiple of the denominators of its
coefficients; equivalently, the least positive integer `d` with `d P ∈ ℤ[X]` (`polyDen_dvd_iff`).

* `squarefree_polyDen_bernoulli_sub`, `prime_dvd_polyDen_bernoulli_sub_iff`: the denominator of
  `B_n(x) - B_n` is squarefree, and a prime `p` divides it iff `s_p(n) ≥ p`;
* `squarefree_polyDen_iterate_derivative`, `prime_dvd_polyDen_iterate_derivative_iff`: for `1 ≤ k ≤ n`
  the denominator of `B_n^{(k)}(x)` is squarefree, and `p` divides it iff `p ∤ n (n - 1) ⋯ (n - k + 1)` and
  `s_p(n - k + 1) ≥ p`;
* `polyDen_bernoulli_sub_eq_a`: the sequence `a` of `formal-conjectures` is this denominator, and
  `bernoulli_sub_den_eq_radical_iff` is Corollary 3 stated with it.
-/

namespace KellnerBernoulli

open Polynomial

/-- The denominator of a polynomial over `ℚ`: the least common multiple of the denominators of its
coefficients.  By `polyDen_dvd_iff` it is the least positive integer `d` with `d P ∈ ℤ[X]`. -/
def polyDen (P : ℚ[X]) : ℕ := P.support.lcm fun i => (P.coeff i).den

theorem polyDen_ne_zero (P : ℚ[X]) : polyDen P ≠ 0 := by
  unfold polyDen
  rw [Ne, Finset.lcm_eq_zero_iff]
  push Not
  intro i _
  exact Rat.den_ne_zero _

theorem den_dvd_polyDen (P : ℚ[X]) (i : ℕ) : (P.coeff i).den ∣ polyDen P := by
  by_cases hi : i ∈ P.support
  · exact Finset.dvd_lcm hi
  · rw [Polynomial.notMem_support_iff.mp hi]
    simp

theorem polyDen_dvd_iff_forall {P : ℚ[X]} {d : ℕ} : polyDen P ∣ d ↔ ∀ i, (P.coeff i).den ∣ d :=
  ⟨fun h i => (den_dvd_polyDen P i).trans h, fun h => Finset.lcm_dvd fun i _ => h i⟩

theorem natCast_mul_den_eq_one_iff (d : ℕ) (q : ℚ) : ((d : ℚ) * q).den = 1 ↔ q.den ∣ d := by
  rw [Rat.mul_den]
  simp only [Rat.num_natCast, Rat.den_natCast, one_mul]
  rw [Int.natAbs_mul, Int.natAbs_natCast, Nat.Coprime.gcd_mul_right_cancel d q.reduced]
  have hpos := q.den_pos
  constructor
  · intro h
    have hg : d.gcd q.den = q.den := by
      have h1 := Nat.div_mul_cancel (Nat.gcd_dvd_right d q.den)
      rw [h, one_mul] at h1
      exact h1
    rw [← hg]
    exact Nat.gcd_dvd_left d q.den
  · intro h
    rw [Nat.gcd_eq_right h, Nat.div_self hpos]

/-- `polyDen P` divides `d` iff `d P` has integral coefficients. -/
theorem polyDen_dvd_iff {P : ℚ[X]} {d : ℕ} : polyDen P ∣ d ↔ IntCoeffs (C (d : ℚ) * P) := by
  rw [polyDen_dvd_iff_forall]
  unfold IntCoeffs
  simp only [Polynomial.coeff_C_mul]
  exact forall_congr' fun i => (natCast_mul_den_eq_one_iff d _).symm

theorem polyDen_eq_one_iff (P : ℚ[X]) : polyDen P = 1 ↔ IntCoeffs P := by
  rw [← Nat.dvd_one, polyDen_dvd_iff_forall]
  simp only [Nat.dvd_one]
  rfl

theorem prime_dvd_polyDen_iff {P : ℚ[X]} {p : ℕ} (hp : p.Prime) :
    p ∣ polyDen P ↔ ∃ i, p ∣ (P.coeff i).den := by
  constructor
  · intro h
    rw [hp.dvd_iff_one_le_factorization (polyDen_ne_zero P)] at h
    unfold polyDen at h
    rw [Finset.factorization_lcm (fun i _ => Rat.den_ne_zero _) p,
      Finset.le_sup_iff (by norm_num)] at h
    obtain ⟨i, _, hi⟩ := h
    exact ⟨i, (hp.dvd_iff_one_le_factorization (Rat.den_ne_zero _)).mpr hi⟩
  · rintro ⟨i, hi⟩
    exact hi.trans (den_dvd_polyDen P i)

theorem squarefree_polyDen {P : ℚ[X]} (h : ∀ i p, (P.coeff i).den.factorization p ≤ 1) :
    Squarefree (polyDen P) := by
  rw [Nat.squarefree_iff_factorization_le_one (polyDen_ne_zero P)]
  intro p
  unfold polyDen
  rw [Finset.factorization_lcm (fun i _ => Rat.den_ne_zero _) p]
  exact Finset.sup_le fun i _ => h i p

theorem not_prime_dvd_den_zero {p : ℕ} (hp : p.Prime) : ¬ p ∣ (0 : ℚ).den := by
  simp only [Rat.den_zero, Nat.dvd_one]
  exact hp.one_lt.ne'

/-! ## Derivatives -/

theorem sub_add_one_dvd_descFactorial {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) :
    (n - k + 1) ∣ n.descFactorial k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.descFactorial_succ]
  exact ⟨_, by rw [show n - k' = n - (k' + 1) + 1 by omega]⟩

/-- Proposition 9, second part: the denominator of `B_n^{(k)}(x)` is squarefree. -/
theorem squarefree_polyDen_iterate_derivative (n k : ℕ) :
    Squarefree (polyDen (derivative^[k] (Polynomial.bernoulli n))) := by
  refine squarefree_polyDen fun i p => ?_
  rw [coeff_iterate_derivative_bernoulli]
  split_ifs
  · exact den_factorization_le_one p _ _
  · simp

/-- Proposition 9, second part: for `1 ≤ k ≤ n`, a prime `p` divides the denominator of `B_n^{(k)}(x)` iff
`p ∤ n (n - 1) ⋯ (n - k + 1)` and `s_p(n - k + 1) ≥ p`. -/
theorem prime_dvd_polyDen_iterate_derivative_iff {n k p : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n)
    (hp : p.Prime) :
    p ∣ polyDen (derivative^[k] (Polynomial.bernoulli n)) ↔
      ¬ p ∣ n.descFactorial k ∧ p ≤ digitSum p (n - k + 1) := by
  rw [prime_dvd_polyDen_iff hp]
  have step : (∃ i, p ∣ ((derivative^[k] (Polynomial.bernoulli n)).coeff i).den) ↔
      ∃ j ≤ n - k, Jset p j ∧ ¬ p ∣ n.descFactorial k * (n - k).choose j := by
    constructor
    · rintro ⟨i, hi⟩
      rw [coeff_iterate_derivative_bernoulli] at hi
      split_ifs at hi with him
      · rw [dvd_den_mul_bernoulli_iff hp] at hi
        refine ⟨n - k - i, by omega, hi.1, ?_⟩
        rw [Nat.choose_symm (by omega)]
        exact hi.2
      · exact absurd hi (not_prime_dvd_den_zero hp)
    · rintro ⟨j, hj, hJ, hdiv⟩
      refine ⟨n - k - j, ?_⟩
      rw [coeff_iterate_derivative_bernoulli, ite_eq_left (by omega), dvd_den_mul_bernoulli_iff hp,
        show n - k - (n - k - j) = j by omega, Nat.choose_symm (by omega)]
      exact ⟨hJ, hdiv⟩
  rw [step, exists_Jset_iff hp]
  have hfac := sub_add_one_dvd_descFactorial hk1 hk
  have hp2 := hp.two_le
  constructor
  · rintro ⟨hD, hle⟩
    have hm : ¬ p ∣ n - k + 1 := fun h => hD (h.trans hfac)
    refine ⟨hD, ?_⟩
    rw [digitSum_succ hp2 hm]
    omega
  · rintro ⟨hD, hle⟩
    have hm : ¬ p ∣ n - k + 1 := fun h => hD (h.trans hfac)
    refine ⟨hD, ?_⟩
    rw [digitSum_succ hp2 hm] at hle
    omega

theorem polyDen_iterate_derivative_of_lt {n k : ℕ} (h : n < k) :
    polyDen (derivative^[k] (Polynomial.bernoulli n)) = 1 :=
  (polyDen_eq_one_iff _).mpr (intCoeffs_iterate_derivative_of_lt n k h)

/-! ## `B_n(x) - B_n` -/

theorem coeff_bernoulli_sub (n i : ℕ) :
    (Polynomial.bernoulli n - C (_root_.bernoulli n)).coeff i =
      if 1 ≤ i ∧ i ≤ n then ((n.choose i : ℕ) : ℚ) * _root_.bernoulli (n - i) else 0 := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_bernoulli]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · have hi0 : i ≠ 0 := by omega
    by_cases hin : i ≤ n
    · rw [ite_eq_left hin, ite_eq_right hi0, ite_eq_left ⟨hi, hin⟩]
      ring
    · rw [ite_eq_right hin, ite_eq_right hi0, ite_eq_right (fun h => hin h.2)]
      ring

/-- Proposition 9, first part: the denominator of `B_n(x) - B_n` is squarefree. -/
theorem squarefree_polyDen_bernoulli_sub (n : ℕ) :
    Squarefree (polyDen (Polynomial.bernoulli n - C (_root_.bernoulli n))) := by
  refine squarefree_polyDen fun i p => ?_
  rw [coeff_bernoulli_sub]
  split_ifs
  · exact den_factorization_le_one p _ _
  · simp

/-- Proposition 9, first part: a prime `p` divides the denominator of `B_n(x) - B_n` iff
`s_p(n) ≥ p`. -/
theorem prime_dvd_polyDen_bernoulli_sub_iff {n p : ℕ} (hp : p.Prime) :
    p ∣ polyDen (Polynomial.bernoulli n - C (_root_.bernoulli n)) ↔ p ≤ digitSum p n := by
  rw [prime_dvd_polyDen_iff hp, ← exists_Jset_lt_iff hp n]
  constructor
  · rintro ⟨i, hi⟩
    rw [coeff_bernoulli_sub] at hi
    split_ifs at hi with h
    · rw [dvd_den_mul_bernoulli_iff hp] at hi
      refine ⟨n - i, by omega, hi.1, ?_⟩
      rw [Nat.choose_symm h.2]
      exact hi.2
    · exact absurd hi (not_prime_dvd_den_zero hp)
  · rintro ⟨j, hj, hJ, hC⟩
    refine ⟨n - j, ?_⟩
    rw [coeff_bernoulli_sub, ite_eq_left ⟨by omega, by omega⟩, dvd_den_mul_bernoulli_iff hp,
      show n - (n - j) = j by omega, Nat.choose_symm (by omega)]
    exact ⟨hJ, hC⟩

/-- The sequence `a` of `formal-conjectures` (OEIS A195441) is the denominator of `B_n(x) - B_n`. -/
theorem polyDen_bernoulli_sub_eq_a {n : ℕ} (hn : 1 ≤ n) :
    polyDen (Polynomial.bernoulli n - C (_root_.bernoulli n)) = a (n - 1) := by
  rw [Nat.Squarefree.ext_iff (squarefree_polyDen_bernoulli_sub n) (a_squarefree _)]
  intro p hp
  rw [prime_dvd_polyDen_bernoulli_sub_iff hp, prime_dvd_a_iff hn hp]

/-- **Corollary 3** in terms of the polynomial: for `n ≥ 1`, the denominator of `B_n(x) - B_n` equals
`rad(n + 1)` iff `n ∈ {3, 5, 8, 9, 11, 27, 29, 35, 59}` ([Kellner 2024, Conjecture 11]). -/
theorem bernoulli_sub_den_eq_radical_iff (h : ThetaBound) {n : ℕ} (hn : 1 ≤ n) :
    polyDen (Polynomial.bernoulli n - C (_root_.bernoulli n)) = UniqueFactorizationMonoid.radical (n + 1) ↔
      n ∈ ({3, 5, 8, 9, 11, 27, 29, 35, 59} : Finset ℕ) := by
  rw [polyDen_bernoulli_sub_eq_a hn, ← Finset.mem_coe, ← oeis_A195441 h]
  simp [hn]

end KellnerBernoulli
