# Bernoulli polynomials with integral derivatives

This repository contains a proof of several conjectures of B. C. Kellner on the denominators of
Bernoulli polynomials, a Lean 4 formalization of most of it, and the computations it uses.

**Main results.** Write `s_p(n)` for the sum of the base-`p` digits of `n`, and `D_n^+` for the product of
the primes `p > √n` with `s_p(n) ≥ p`.

1. For every `n > 192` there is a prime `p > √n` with `s_p(n) ≥ p`
   (Kellner 2017, Conjecture 1; Kellner 2024, Conjecture 2(i)). The exceptions `n ≤ 192` are
   1, 2, 4, 6, 10, 11, 12, 15, 16, 28, 29, 30, 35, 36, 58, 59, 60, 69, 70, 78, 79, 80, 174, 190, 191, 192.
   More precisely, `ω(D_n^+) ≥ k` for `n > b_k`, with `b_1, …, b_24 = 192, 1080, 2014, 2430, 3360, 5076,
   5796, 11824, 13440, 13440, 15438, 17748, 26640, 26640, 32128, 32130, 37570, 44516, 44520, 53760, 62616,
   62618, 63596, 75140`, and `ω(D_{b_k}^+) = k − 1` (`k − 2` for `k = 10, 14`, where `b_k = b_{k−1}`).
2. For `n ≥ 1`, the derivative `B_n'(x)` has integer coefficients if and only if
   `n ∈ {1, 2, 4, 6, 10, 12, 28, 30, 36, 60}` (Kellner 2024, Conjecture 1(ii); OEIS A094960).
3. For `n ≥ 1`, the denominator of `B_n(x) - B_n` equals the radical of `n + 1` if and only if
   `n ∈ {3, 5, 8, 9, 11, 27, 29, 35, 59}` (Kellner 2024, Conjecture 11; OEIS A195441).
4. The sets of `n` for which the second and third derivatives of `B_n(x)` have integer coefficients
   are the ones conjectured by Kellner (2024, Conjecture 15; OEIS A366169, A366186). The paper also
   determines these sets for the `k`-th derivative, `k ≤ 24`, which confirms the terms of OEIS A366187
   and the b-file of A366188.
5. The second inequality of Kellner 2017, Conjecture 1, and a conjecture of M. Alekseyev in OEIS A094960.
6. **The integral index** `a(n)`, the least `k` with `B_n^{(k)}(x) ∈ ℤ[x]` (OEIS A366189; Section 7 of the paper).
   For every `k ≥ 1` the least `n` with `a(n) > k` is `(k+1)p − 1`, where `p` is the least prime `> k`
   (Theorem 10). Hence `a(n) ≤ ⌈√(n+2)⌉ − 1` for all `n`, with equality when `n + 1` is the square of a prime,
   and the first `n` with `a(n) = k` is `kq − 1`, where `q` is the least prime `≥ k` (Corollary 11).
7. **Explicit bounds for all `k`.** `ω(D_n^+) > √n / (4 log² n)` for every `n > 192` (Theorem 12). Hence
   `b_k < 10^5 k² log⁴(k+1)` and `k² + 2k − 1 ≤ max S̄_k < 10^5 k² log⁴(k+1) + k` for every `k`, and
   `(√n − 1)/(4 log² n) < a(n) < √(n+2)` (Corollary 13). This makes effective Kellner's theorem that every
   `S̄_k` is finite, i.e. that every value occurs only finitely often in A366189 (the conjecture stated there).
   We conjecture `a(n) ~ √n`; the minimum of `a(n)/√n` over `[2^j, 2^(j+1))` rises to 0.76 at `j = 23`.

Results 2, 5 and the first part of 1 need only one prime; results 3 and 4 use the bounds for `k ≥ 2`, and
the table in 4 uses the stronger bounds of Sections 3 and 4 of the paper. Result 6 needs only the criterion
for the denominators (Proposition 9); result 7 uses the estimate of Section 3 and a computation.

The paper is [`paper/kellner.pdf`](paper/kellner.pdf).

**Status.** Written with the assistance of a large language model (Claude, by Anthropic), which was used
for the proof, the computations, the Lean formalization and the writing. Not yet refereed by a journal.

## The idea

If `m > √n`, then `n` has at most two digits in base `m`, and `s_m(n) ≥ m` fails only when
`⌊n/(m−1)⌋ = ⌊n/m⌋` or `m − 1` divides `n`. A telescoping argument shows that this happens for fewer than
`4 + 2U²/(s+U)` of the integers `m` in `(s, s + U]`, `s = ⌊√n⌋`. An explicit form of the prime number
theorem then gives many primes among the others, for `s ≥ 678407`; a computation covers the rest.

For the integral index: if `p > √m` and `s_p(m) ≥ p`, then `p` divides `m + j` for some `1 ≤ j ≤ ⌊m/p⌋`. So a
prime `p > k` can keep `B_n^{(k)}(x)`, `m = n − k + 1`, from being integral only if `m ≥ kp + (p − k)`; this gives
Theorem 10, and the good primes `p > √m` of Theorem 12 give the lower bounds.

## The Lean formalization

`lake exe cache get && lake build` checks everything (about 3 minutes on a fast machine, longer on CI).
There is no `sorry`, no `native_decide` and no added axiom. `lake env lean scripts/Axioms.lean` prints
the axioms of the main results and **fails** unless every declaration of the project depends only on
`propext`, `Classical.choice` and `Quot.sound`; the CI runs it after the build. All computations are done
by the kernel (`decide +kernel`). The compiled proofs can also be replayed module by module with
`lake env leanchecker KellnerBernoulli.<Module>` (one module at a time; each needs up to a few GB).

**The one external input.** The proof for large `n` uses the explicit bound

    |θ(x) − x| ≤ x / (40 log x)   for x ≥ 4·10^6,   θ(x) = Σ_{p ≤ x} log p,

which Rosser and Schoenfeld proved in 1975 (with `<`, for `x ≥ 678407`; Math. Comp. 29, 243–269,
Corollary 2, (5.7)); Dusart (2018) proved a stronger bound. Both results are unconditional. This bound is
not in Mathlib, and we have not formalized it: the published proofs rely on explicit information about
the zeros of the Riemann zeta function, which is not available in Mathlib. It is therefore an explicit
hypothesis `h : ThetaBound` of the theorems marked "hyp." below, and not an axiom. The lemmas
`ThetaBound.of_rosserSchoenfeld` and `ThetaBound.of_dusart` derive it from the published statements.
For `n < 1.6·10^13` Theorem 1 (for `k ≤ 3`) is proved without this hypothesis.

**What is formalized.** "proved": no hypothesis. "hyp.": assuming `ThetaBound`. "comp.": established
only by the programs in `verify/` (see below), not in Lean. "paper": proved in the paper only (a short,
elementary proof; `verify/index.cpp` checks it for `k ≤ 4092` and `n < 2^24`). Theorem 10 and Corollary 11 do
not need `ThetaBound` and would be natural next targets for the formalization.

| Result (paper) | Lean name | Status |
|---|---|---|
| Lemmas 7, 8 (counting lemma, constant 4) | `bad_imp`, `div_pred_le`, `card_bad_mul_lt` | proved |
| Theorem 1, first statement | `kellner_conjecture`, `kellner_exceptions`; `kellner_conjecture_of_lt` (`n < 1.6·10^13`) | hyp.; proved for `n < 1.6·10^13` |
| Theorem 1 for `k ≤ 3`, and `ω(D_{b_k}^+) = k − 1` for `k ≤ 3` | `card_goodPrimes_ge_of_thetaBound`, `card_goodPrimes_ge_of_lt`, `card_goodPrimes_thresholds` | hyp.; proved for `n < 1.6·10^13` |
| Theorem 1 for `4 ≤ k ≤ 24`, the bounds (3.2) and (4.1) | — | comp. |
| Proposition 9 (denominators) | `squarefree_polyDen_bernoulli_sub`, `prime_dvd_polyDen_bernoulli_sub_iff`, `squarefree_polyDen_iterate_derivative`, `prime_dvd_polyDen_iterate_derivative_iff` | proved |
| Corollary 2: `B_n'(x) ∈ ℤ[x]` | `bernoulli_derivative_intCoeffs_iff`, `bernoulli_derivative_mem_lifts_iff` | hyp. |
| Corollary 3 (OEIS A195441) | `bernoulli_sub_den_eq_radical_iff`, `oeis_A195441` | hyp. |
| Corollary 4: second and third derivatives | `bernoulli_iterate_derivative_two`, `bernoulli_iterate_derivative_three` | hyp. |
| Corollary 4: table for `4 ≤ k ≤ 24` (A366187, A366188) | — | comp. |
| Corollary 5 (Kellner 2017, Conjecture 1) | `kellner2017` | hyp. |
| Corollary 6 (Alekseyev's conjecture) | `alekseyev` | hyp. |
| Theorem 10, Corollary 11 (integral index: first gap, `a(n) ≤ ⌈√(n+2)⌉ − 1`) | — | paper |
| Theorem 12, Corollary 13 (`ω(D_n^+) > √n/(4 log² n)`, effective bounds for all `k`) | — | comp. |

`(goodPrimes n).card` is `ω(D_n^+)` (`mem_goodPrimes_iff_digits`), and `polyDen P` is the denominator of a
polynomial `P ∈ ℚ[X]`, the least positive integer `d` with `d P ∈ ℤ[X]` (`polyDen_dvd_iff`).

**`formal-conjectures`.** The statement `oeis_A195441` has the same definition of `a` and the same
conclusion as `OeisA195441.conjecture` in `google-deepmind/formal-conjectures`, but it carries the
hypothesis `ThetaBound`. It therefore proves that statement only under this hypothesis; it does not fill
the unconditional statement there.

**Differences from the paper.** The formal proof of Theorem 1 shows `ω(D_n^+) ≥ 3` (not more) for
`n > 2014`, which is all the formal corollaries need. It uses `ThetaBound` from `⌊√n⌋ ≥ 4·10^6` on
(the paper uses it from `10^9` on), and replaces the computation of Section 4 by a kernel computation for
`2015 ≤ n < 1.6·10^13`.

Files in `KellnerBernoulli/`:

- `Counting.lean`: the two-digit formula and the counting lemma (Lemmas 7, 8 of the paper);
- `Large.lean`: the estimate for `⌊√n⌋ ≥ 4·10^6`, from `ThetaBound`;
- `Data.lean`, `Finite.lean`, `FiniteChain.lean`, `FiniteWindow.lean`: lists of primes and their kernel check
  for `2015 ≤ n < 1.6·10^13` (the lists are generated by `scripts/gen_data.py`; they need not be trusted,
  since primality, order and every property used is checked by the kernel);
- `Digits.lean`, `Criterion.lean`: digit sums, von Staudt–Clausen and Kummer, and the integrality criterion
  for derivatives;
- `SmallCases.lean`: kernel-checked tables for `n ≤ 2016`;
- `Main.lean`, `Corollaries.lean`, `Denominators.lean`: the results.

## Other computations

`verify/` contains separate C++ and Python programs for the computations in the paper, which go
further than the Lean check (up to `n < 10^18`, the tables in Theorem 1 and Corollary 4, and Section 7):

    cd verify && ./run_all.sh            # everything (about 37 CPU-minutes; a few minutes with many cores)
    cd verify && QUICK=1 ./run_all.sh    # only what the proofs need (about 3 minutes)

The script compares every value stated in the paper with the output of the programs and exits with a
non-zero status if a program fails or a value differs. The programs use integer arithmetic only (with
rational lower bounds for logarithms in `omega_bound.py`). Since (3.2) of the paper covers `s ≥ 678407`, the
proofs need the computation of Section 4 only for `s < 678407`; `QUICK=1` checks (4.1) only in that range.
The new programs are `index.cpp` (the integral index `a(n)` for `n < 2^24`: Theorem 10, Corollary 11, the
table of Corollary 4 recomputed, the data for Conjecture 14) and `omega_bound.py` (the constants of Section 3,
and Theorem 12). The CI runs `QUICK=1 ./verify/run_all.sh` on every push (`.github/workflows/verify.yml`).

## References

- B. C. Kellner, *On a product of certain primes*, J. Number Theory 179 (2017), 126–141.
- B. C. Kellner, *On the finiteness of Bernoulli polynomials whose derivative has only integral coefficients*,
  J. Integer Seq. 27 (2024), Article 24.2.8.
- B. C. Kellner, J. Sondow, *Power-sum denominators*, Amer. Math. Monthly 124 (2017), 695–709.
- O. Bordellès, *On a conjecture of B. C. Kellner*, preprint (2017), arXiv:1705.06128.
- O. Bordellès, F. Luca, P. Moree, I. E. Shparlinski, *Denominators of Bernoulli polynomials*,
  Mathematika 64 (2018), 519–541.
- J. B. Rosser, L. Schoenfeld, *Sharper bounds for the Chebyshev functions θ(x) and ψ(x)*,
  Math. Comp. 29 (1975), 243–269.
- S. Broadbent, H. Kadiri, A. Lumley, N. Ng, K. Wilk, *Sharper bounds for the Chebyshev function θ(x)*,
  Math. Comp. 90 (2021), 2281–2315.
- P. Dusart, *Explicit estimates of some functions over primes*, Ramanujan J. 45 (2018), 227–251.

## License

MIT, see [`LICENSE`](LICENSE).
