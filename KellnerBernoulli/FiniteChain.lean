import KellnerBernoulli.Finite

/-!
# Kernel computation, part 1: `2015 ≤ n < 10 ^ 8`

One theorem `chainSeg i` per segment `(100 i) ^ 2 ≤ n < (100 (i + 1)) ^ 2`, so that the kernel checks (and
an external checker replays) the segments separately.
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

theorem chainSeg0 :
    loop ((100 * (0 + 1)) * (100 * (0 + 1))) 2000 (segLo 0) Data.chain = true := by
  decide +kernel

theorem chainSeg1 :
    loop ((100 * (1 + 1)) * (100 * (1 + 1))) 2000 (segLo 1) Data.chain = true := by
  decide +kernel

theorem chainSeg2 :
    loop ((100 * (2 + 1)) * (100 * (2 + 1))) 2000 (segLo 2) Data.chain = true := by
  decide +kernel

theorem chainSeg3 :
    loop ((100 * (3 + 1)) * (100 * (3 + 1))) 2000 (segLo 3) Data.chain = true := by
  decide +kernel

theorem chainSeg4 :
    loop ((100 * (4 + 1)) * (100 * (4 + 1))) 2000 (segLo 4) Data.chain = true := by
  decide +kernel

theorem chainSeg5 :
    loop ((100 * (5 + 1)) * (100 * (5 + 1))) 2000 (segLo 5) Data.chain = true := by
  decide +kernel

theorem chainSeg6 :
    loop ((100 * (6 + 1)) * (100 * (6 + 1))) 2000 (segLo 6) Data.chain = true := by
  decide +kernel

theorem chainSeg7 :
    loop ((100 * (7 + 1)) * (100 * (7 + 1))) 2000 (segLo 7) Data.chain = true := by
  decide +kernel

theorem chainSeg8 :
    loop ((100 * (8 + 1)) * (100 * (8 + 1))) 2000 (segLo 8) Data.chain = true := by
  decide +kernel

theorem chainSeg9 :
    loop ((100 * (9 + 1)) * (100 * (9 + 1))) 2000 (segLo 9) Data.chain = true := by
  decide +kernel

theorem chainSeg10 :
    loop ((100 * (10 + 1)) * (100 * (10 + 1))) 2000 (segLo 10) Data.chain = true := by
  decide +kernel

theorem chainSeg11 :
    loop ((100 * (11 + 1)) * (100 * (11 + 1))) 2000 (segLo 11) Data.chain = true := by
  decide +kernel

theorem chainSeg12 :
    loop ((100 * (12 + 1)) * (100 * (12 + 1))) 2000 (segLo 12) Data.chain = true := by
  decide +kernel

theorem chainSeg13 :
    loop ((100 * (13 + 1)) * (100 * (13 + 1))) 2000 (segLo 13) Data.chain = true := by
  decide +kernel

theorem chainSeg14 :
    loop ((100 * (14 + 1)) * (100 * (14 + 1))) 2000 (segLo 14) Data.chain = true := by
  decide +kernel

theorem chainSeg15 :
    loop ((100 * (15 + 1)) * (100 * (15 + 1))) 2000 (segLo 15) Data.chain = true := by
  decide +kernel

theorem chainSeg16 :
    loop ((100 * (16 + 1)) * (100 * (16 + 1))) 2000 (segLo 16) Data.chain = true := by
  decide +kernel

theorem chainSeg17 :
    loop ((100 * (17 + 1)) * (100 * (17 + 1))) 2000 (segLo 17) Data.chain = true := by
  decide +kernel

theorem chainSeg18 :
    loop ((100 * (18 + 1)) * (100 * (18 + 1))) 2000 (segLo 18) Data.chain = true := by
  decide +kernel

theorem chainSeg19 :
    loop ((100 * (19 + 1)) * (100 * (19 + 1))) 2000 (segLo 19) Data.chain = true := by
  decide +kernel

theorem chainSeg20 :
    loop ((100 * (20 + 1)) * (100 * (20 + 1))) 2000 (segLo 20) Data.chain = true := by
  decide +kernel

theorem chainSeg21 :
    loop ((100 * (21 + 1)) * (100 * (21 + 1))) 2000 (segLo 21) Data.chain = true := by
  decide +kernel

theorem chainSeg22 :
    loop ((100 * (22 + 1)) * (100 * (22 + 1))) 2000 (segLo 22) Data.chain = true := by
  decide +kernel

theorem chainSeg23 :
    loop ((100 * (23 + 1)) * (100 * (23 + 1))) 2000 (segLo 23) Data.chain = true := by
  decide +kernel

theorem chainSeg24 :
    loop ((100 * (24 + 1)) * (100 * (24 + 1))) 2000 (segLo 24) Data.chain = true := by
  decide +kernel

theorem chainSeg25 :
    loop ((100 * (25 + 1)) * (100 * (25 + 1))) 2000 (segLo 25) Data.chain = true := by
  decide +kernel

theorem chainSeg26 :
    loop ((100 * (26 + 1)) * (100 * (26 + 1))) 2000 (segLo 26) Data.chain = true := by
  decide +kernel

theorem chainSeg27 :
    loop ((100 * (27 + 1)) * (100 * (27 + 1))) 2000 (segLo 27) Data.chain = true := by
  decide +kernel

theorem chainSeg28 :
    loop ((100 * (28 + 1)) * (100 * (28 + 1))) 2000 (segLo 28) Data.chain = true := by
  decide +kernel

theorem chainSeg29 :
    loop ((100 * (29 + 1)) * (100 * (29 + 1))) 2000 (segLo 29) Data.chain = true := by
  decide +kernel

theorem chainSeg30 :
    loop ((100 * (30 + 1)) * (100 * (30 + 1))) 2000 (segLo 30) Data.chain = true := by
  decide +kernel

theorem chainSeg31 :
    loop ((100 * (31 + 1)) * (100 * (31 + 1))) 2000 (segLo 31) Data.chain = true := by
  decide +kernel

theorem chainSeg32 :
    loop ((100 * (32 + 1)) * (100 * (32 + 1))) 2000 (segLo 32) Data.chain = true := by
  decide +kernel

theorem chainSeg33 :
    loop ((100 * (33 + 1)) * (100 * (33 + 1))) 2000 (segLo 33) Data.chain = true := by
  decide +kernel

theorem chainSeg34 :
    loop ((100 * (34 + 1)) * (100 * (34 + 1))) 2000 (segLo 34) Data.chain = true := by
  decide +kernel

theorem chainSeg35 :
    loop ((100 * (35 + 1)) * (100 * (35 + 1))) 2000 (segLo 35) Data.chain = true := by
  decide +kernel

theorem chainSeg36 :
    loop ((100 * (36 + 1)) * (100 * (36 + 1))) 2000 (segLo 36) Data.chain = true := by
  decide +kernel

theorem chainSeg37 :
    loop ((100 * (37 + 1)) * (100 * (37 + 1))) 2000 (segLo 37) Data.chain = true := by
  decide +kernel

theorem chainSeg38 :
    loop ((100 * (38 + 1)) * (100 * (38 + 1))) 2000 (segLo 38) Data.chain = true := by
  decide +kernel

theorem chainSeg39 :
    loop ((100 * (39 + 1)) * (100 * (39 + 1))) 2000 (segLo 39) Data.chain = true := by
  decide +kernel

theorem chainSeg40 :
    loop ((100 * (40 + 1)) * (100 * (40 + 1))) 2000 (segLo 40) Data.chain = true := by
  decide +kernel

theorem chainSeg41 :
    loop ((100 * (41 + 1)) * (100 * (41 + 1))) 2000 (segLo 41) Data.chain = true := by
  decide +kernel

theorem chainSeg42 :
    loop ((100 * (42 + 1)) * (100 * (42 + 1))) 2000 (segLo 42) Data.chain = true := by
  decide +kernel

theorem chainSeg43 :
    loop ((100 * (43 + 1)) * (100 * (43 + 1))) 2000 (segLo 43) Data.chain = true := by
  decide +kernel

theorem chainSeg44 :
    loop ((100 * (44 + 1)) * (100 * (44 + 1))) 2000 (segLo 44) Data.chain = true := by
  decide +kernel

theorem chainSeg45 :
    loop ((100 * (45 + 1)) * (100 * (45 + 1))) 2000 (segLo 45) Data.chain = true := by
  decide +kernel

theorem chainSeg46 :
    loop ((100 * (46 + 1)) * (100 * (46 + 1))) 2000 (segLo 46) Data.chain = true := by
  decide +kernel

theorem chainSeg47 :
    loop ((100 * (47 + 1)) * (100 * (47 + 1))) 2000 (segLo 47) Data.chain = true := by
  decide +kernel

theorem chainSeg48 :
    loop ((100 * (48 + 1)) * (100 * (48 + 1))) 2000 (segLo 48) Data.chain = true := by
  decide +kernel

theorem chainSeg49 :
    loop ((100 * (49 + 1)) * (100 * (49 + 1))) 2000 (segLo 49) Data.chain = true := by
  decide +kernel

theorem chainSeg50 :
    loop ((100 * (50 + 1)) * (100 * (50 + 1))) 2000 (segLo 50) Data.chain = true := by
  decide +kernel

theorem chainSeg51 :
    loop ((100 * (51 + 1)) * (100 * (51 + 1))) 2000 (segLo 51) Data.chain = true := by
  decide +kernel

theorem chainSeg52 :
    loop ((100 * (52 + 1)) * (100 * (52 + 1))) 2000 (segLo 52) Data.chain = true := by
  decide +kernel

theorem chainSeg53 :
    loop ((100 * (53 + 1)) * (100 * (53 + 1))) 2000 (segLo 53) Data.chain = true := by
  decide +kernel

theorem chainSeg54 :
    loop ((100 * (54 + 1)) * (100 * (54 + 1))) 2000 (segLo 54) Data.chain = true := by
  decide +kernel

theorem chainSeg55 :
    loop ((100 * (55 + 1)) * (100 * (55 + 1))) 2000 (segLo 55) Data.chain = true := by
  decide +kernel

theorem chainSeg56 :
    loop ((100 * (56 + 1)) * (100 * (56 + 1))) 2000 (segLo 56) Data.chain = true := by
  decide +kernel

theorem chainSeg57 :
    loop ((100 * (57 + 1)) * (100 * (57 + 1))) 2000 (segLo 57) Data.chain = true := by
  decide +kernel

theorem chainSeg58 :
    loop ((100 * (58 + 1)) * (100 * (58 + 1))) 2000 (segLo 58) Data.chain = true := by
  decide +kernel

theorem chainSeg59 :
    loop ((100 * (59 + 1)) * (100 * (59 + 1))) 2000 (segLo 59) Data.chain = true := by
  decide +kernel

theorem chainSeg60 :
    loop ((100 * (60 + 1)) * (100 * (60 + 1))) 2000 (segLo 60) Data.chain = true := by
  decide +kernel

theorem chainSeg61 :
    loop ((100 * (61 + 1)) * (100 * (61 + 1))) 2000 (segLo 61) Data.chain = true := by
  decide +kernel

theorem chainSeg62 :
    loop ((100 * (62 + 1)) * (100 * (62 + 1))) 2000 (segLo 62) Data.chain = true := by
  decide +kernel

theorem chainSeg63 :
    loop ((100 * (63 + 1)) * (100 * (63 + 1))) 2000 (segLo 63) Data.chain = true := by
  decide +kernel

theorem chainSeg64 :
    loop ((100 * (64 + 1)) * (100 * (64 + 1))) 2000 (segLo 64) Data.chain = true := by
  decide +kernel

theorem chainSeg65 :
    loop ((100 * (65 + 1)) * (100 * (65 + 1))) 2000 (segLo 65) Data.chain = true := by
  decide +kernel

theorem chainSeg66 :
    loop ((100 * (66 + 1)) * (100 * (66 + 1))) 2000 (segLo 66) Data.chain = true := by
  decide +kernel

theorem chainSeg67 :
    loop ((100 * (67 + 1)) * (100 * (67 + 1))) 2000 (segLo 67) Data.chain = true := by
  decide +kernel

theorem chainSeg68 :
    loop ((100 * (68 + 1)) * (100 * (68 + 1))) 2000 (segLo 68) Data.chain = true := by
  decide +kernel

theorem chainSeg69 :
    loop ((100 * (69 + 1)) * (100 * (69 + 1))) 2000 (segLo 69) Data.chain = true := by
  decide +kernel

theorem chainSeg70 :
    loop ((100 * (70 + 1)) * (100 * (70 + 1))) 2000 (segLo 70) Data.chain = true := by
  decide +kernel

theorem chainSeg71 :
    loop ((100 * (71 + 1)) * (100 * (71 + 1))) 2000 (segLo 71) Data.chain = true := by
  decide +kernel

theorem chainSeg72 :
    loop ((100 * (72 + 1)) * (100 * (72 + 1))) 2000 (segLo 72) Data.chain = true := by
  decide +kernel

theorem chainSeg73 :
    loop ((100 * (73 + 1)) * (100 * (73 + 1))) 2000 (segLo 73) Data.chain = true := by
  decide +kernel

theorem chainSeg74 :
    loop ((100 * (74 + 1)) * (100 * (74 + 1))) 2000 (segLo 74) Data.chain = true := by
  decide +kernel

theorem chainSeg75 :
    loop ((100 * (75 + 1)) * (100 * (75 + 1))) 2000 (segLo 75) Data.chain = true := by
  decide +kernel

theorem chainSeg76 :
    loop ((100 * (76 + 1)) * (100 * (76 + 1))) 2000 (segLo 76) Data.chain = true := by
  decide +kernel

theorem chainSeg77 :
    loop ((100 * (77 + 1)) * (100 * (77 + 1))) 2000 (segLo 77) Data.chain = true := by
  decide +kernel

theorem chainSeg78 :
    loop ((100 * (78 + 1)) * (100 * (78 + 1))) 2000 (segLo 78) Data.chain = true := by
  decide +kernel

theorem chainSeg79 :
    loop ((100 * (79 + 1)) * (100 * (79 + 1))) 2000 (segLo 79) Data.chain = true := by
  decide +kernel

theorem chainSeg80 :
    loop ((100 * (80 + 1)) * (100 * (80 + 1))) 2000 (segLo 80) Data.chain = true := by
  decide +kernel

theorem chainSeg81 :
    loop ((100 * (81 + 1)) * (100 * (81 + 1))) 2000 (segLo 81) Data.chain = true := by
  decide +kernel

theorem chainSeg82 :
    loop ((100 * (82 + 1)) * (100 * (82 + 1))) 2000 (segLo 82) Data.chain = true := by
  decide +kernel

theorem chainSeg83 :
    loop ((100 * (83 + 1)) * (100 * (83 + 1))) 2000 (segLo 83) Data.chain = true := by
  decide +kernel

theorem chainSeg84 :
    loop ((100 * (84 + 1)) * (100 * (84 + 1))) 2000 (segLo 84) Data.chain = true := by
  decide +kernel

theorem chainSeg85 :
    loop ((100 * (85 + 1)) * (100 * (85 + 1))) 2000 (segLo 85) Data.chain = true := by
  decide +kernel

theorem chainSeg86 :
    loop ((100 * (86 + 1)) * (100 * (86 + 1))) 2000 (segLo 86) Data.chain = true := by
  decide +kernel

theorem chainSeg87 :
    loop ((100 * (87 + 1)) * (100 * (87 + 1))) 2000 (segLo 87) Data.chain = true := by
  decide +kernel

theorem chainSeg88 :
    loop ((100 * (88 + 1)) * (100 * (88 + 1))) 2000 (segLo 88) Data.chain = true := by
  decide +kernel

theorem chainSeg89 :
    loop ((100 * (89 + 1)) * (100 * (89 + 1))) 2000 (segLo 89) Data.chain = true := by
  decide +kernel

theorem chainSeg90 :
    loop ((100 * (90 + 1)) * (100 * (90 + 1))) 2000 (segLo 90) Data.chain = true := by
  decide +kernel

theorem chainSeg91 :
    loop ((100 * (91 + 1)) * (100 * (91 + 1))) 2000 (segLo 91) Data.chain = true := by
  decide +kernel

theorem chainSeg92 :
    loop ((100 * (92 + 1)) * (100 * (92 + 1))) 2000 (segLo 92) Data.chain = true := by
  decide +kernel

theorem chainSeg93 :
    loop ((100 * (93 + 1)) * (100 * (93 + 1))) 2000 (segLo 93) Data.chain = true := by
  decide +kernel

theorem chainSeg94 :
    loop ((100 * (94 + 1)) * (100 * (94 + 1))) 2000 (segLo 94) Data.chain = true := by
  decide +kernel

theorem chainSeg95 :
    loop ((100 * (95 + 1)) * (100 * (95 + 1))) 2000 (segLo 95) Data.chain = true := by
  decide +kernel

theorem chainSeg96 :
    loop ((100 * (96 + 1)) * (100 * (96 + 1))) 2000 (segLo 96) Data.chain = true := by
  decide +kernel

theorem chainSeg97 :
    loop ((100 * (97 + 1)) * (100 * (97 + 1))) 2000 (segLo 97) Data.chain = true := by
  decide +kernel

theorem chainSeg98 :
    loop ((100 * (98 + 1)) * (100 * (98 + 1))) 2000 (segLo 98) Data.chain = true := by
  decide +kernel

theorem chainSeg99 :
    loop ((100 * (99 + 1)) * (100 * (99 + 1))) 2000 (segLo 99) Data.chain = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
theorem chainCheck_true : chainCheck = true := by
  unfold chainCheck
  apply List.all_eq_true.mpr
  intro i hi
  have hi' : i < 100 := List.mem_range.mp hi
  interval_cases i
  exacts [chainSeg0, chainSeg1, chainSeg2, chainSeg3, chainSeg4, chainSeg5, chainSeg6,
    chainSeg7, chainSeg8, chainSeg9, chainSeg10, chainSeg11, chainSeg12, chainSeg13, chainSeg14,
    chainSeg15, chainSeg16, chainSeg17, chainSeg18, chainSeg19, chainSeg20, chainSeg21,
    chainSeg22, chainSeg23, chainSeg24, chainSeg25, chainSeg26, chainSeg27, chainSeg28,
    chainSeg29, chainSeg30, chainSeg31, chainSeg32, chainSeg33, chainSeg34, chainSeg35,
    chainSeg36, chainSeg37, chainSeg38, chainSeg39, chainSeg40, chainSeg41, chainSeg42,
    chainSeg43, chainSeg44, chainSeg45, chainSeg46, chainSeg47, chainSeg48, chainSeg49,
    chainSeg50, chainSeg51, chainSeg52, chainSeg53, chainSeg54, chainSeg55, chainSeg56,
    chainSeg57, chainSeg58, chainSeg59, chainSeg60, chainSeg61, chainSeg62, chainSeg63,
    chainSeg64, chainSeg65, chainSeg66, chainSeg67, chainSeg68, chainSeg69, chainSeg70,
    chainSeg71, chainSeg72, chainSeg73, chainSeg74, chainSeg75, chainSeg76, chainSeg77,
    chainSeg78, chainSeg79, chainSeg80, chainSeg81, chainSeg82, chainSeg83, chainSeg84,
    chainSeg85, chainSeg86, chainSeg87, chainSeg88, chainSeg89, chainSeg90, chainSeg91,
    chainSeg92, chainSeg93, chainSeg94, chainSeg95, chainSeg96, chainSeg97, chainSeg98,
    chainSeg99]

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
