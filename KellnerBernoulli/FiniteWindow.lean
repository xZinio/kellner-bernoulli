import KellnerBernoulli.FiniteChain

/-!
# Kernel computation, part 2: `9973 ≤ ⌊√n⌋ < 4 * 10 ^ 6`

One theorem per block of the list `Data.windows`, so that the kernel can check them in parallel.
-/

namespace KellnerBernoulli

theorem window0_ok :
    (allR isPrime Data.window0 && incr Data.window0) = true ∧ cover (Data.window1.headD 0) Data.window0 = true := by
  decide +kernel

theorem window1_ok :
    (allR isPrime Data.window1 && incr Data.window1) = true ∧ cover (Data.window2.headD 0) Data.window1 = true := by
  decide +kernel

theorem window2_ok :
    (allR isPrime Data.window2 && incr Data.window2) = true ∧ cover (Data.window3.headD 0) Data.window2 = true := by
  decide +kernel

theorem window3_ok :
    (allR isPrime Data.window3 && incr Data.window3) = true ∧ cover (Data.window4.headD 0) Data.window3 = true := by
  decide +kernel

theorem window4_ok :
    (allR isPrime Data.window4 && incr Data.window4) = true ∧ cover (Data.window5.headD 0) Data.window4 = true := by
  decide +kernel

theorem window5_ok :
    (allR isPrime Data.window5 && incr Data.window5) = true ∧ cover (Data.window6.headD 0) Data.window5 = true := by
  decide +kernel

theorem window6_ok :
    (allR isPrime Data.window6 && incr Data.window6) = true ∧ cover (Data.window7.headD 0) Data.window6 = true := by
  decide +kernel

theorem window7_ok :
    (allR isPrime Data.window7 && incr Data.window7) = true ∧ cover (Data.window8.headD 0) Data.window7 = true := by
  decide +kernel

theorem window8_ok :
    (allR isPrime Data.window8 && incr Data.window8) = true ∧ cover (Data.window9.headD 0) Data.window8 = true := by
  decide +kernel

theorem window9_ok :
    (allR isPrime Data.window9 && incr Data.window9) = true ∧ cover (Data.window10.headD 0) Data.window9 = true := by
  decide +kernel

theorem window10_ok :
    (allR isPrime Data.window10 && incr Data.window10) = true ∧ cover (Data.window11.headD 0) Data.window10 = true := by
  decide +kernel

theorem window11_ok :
    (allR isPrime Data.window11 && incr Data.window11) = true ∧ cover (Data.window12.headD 0) Data.window11 = true := by
  decide +kernel

theorem window12_ok :
    (allR isPrime Data.window12 && incr Data.window12) = true ∧ cover (Data.window13.headD 0) Data.window12 = true := by
  decide +kernel

theorem window13_ok :
    (allR isPrime Data.window13 && incr Data.window13) = true ∧ cover (Data.window14.headD 0) Data.window13 = true := by
  decide +kernel

theorem window14_ok :
    (allR isPrime Data.window14 && incr Data.window14) = true ∧ cover (Data.window15.headD 0) Data.window14 = true := by
  decide +kernel

theorem window15_ok :
    (allR isPrime Data.window15 && incr Data.window15) = true ∧ cover (Data.window16.headD 0) Data.window15 = true := by
  decide +kernel

theorem window16_ok :
    (allR isPrime Data.window16 && incr Data.window16) = true ∧ cover (Data.window17.headD 0) Data.window16 = true := by
  decide +kernel

theorem window17_ok :
    (allR isPrime Data.window17 && incr Data.window17) = true ∧ cover (Data.window18.headD 0) Data.window17 = true := by
  decide +kernel

theorem window18_ok :
    (allR isPrime Data.window18 && incr Data.window18) = true ∧ cover (Data.window19.headD 0) Data.window18 = true := by
  decide +kernel

theorem window19_ok :
    (allR isPrime Data.window19 && incr Data.window19) = true ∧ cover (Data.window20.headD 0) Data.window19 = true := by
  decide +kernel

theorem window20_ok :
    (allR isPrime Data.window20 && incr Data.window20) = true ∧ cover (Data.window21.headD 0) Data.window20 = true := by
  decide +kernel

theorem window21_ok :
    (allR isPrime Data.window21 && incr Data.window21) = true ∧ cover (Data.window22.headD 0) Data.window21 = true := by
  decide +kernel

theorem window22_ok :
    (allR isPrime Data.window22 && incr Data.window22) = true ∧ cover (Data.window23.headD 0) Data.window22 = true := by
  decide +kernel

theorem window23_ok :
    (allR isPrime Data.window23 && incr Data.window23) = true ∧ cover (Data.window24.headD 0) Data.window23 = true := by
  decide +kernel

theorem window24_ok :
    (allR isPrime Data.window24 && incr Data.window24) = true ∧ cover (Data.window25.headD 0) Data.window24 = true := by
  decide +kernel

theorem window25_ok :
    (allR isPrime Data.window25 && incr Data.window25) = true ∧ cover (Data.window26.headD 0) Data.window25 = true := by
  decide +kernel

theorem window26_ok :
    (allR isPrime Data.window26 && incr Data.window26) = true ∧ cover (Data.window27.headD 0) Data.window26 = true := by
  decide +kernel

theorem window27_ok :
    (allR isPrime Data.window27 && incr Data.window27) = true ∧ cover (Data.window28.headD 0) Data.window27 = true := by
  decide +kernel

theorem window28_ok :
    (allR isPrime Data.window28 && incr Data.window28) = true ∧ cover (Data.window29.headD 0) Data.window28 = true := by
  decide +kernel

theorem window29_ok :
    (allR isPrime Data.window29 && incr Data.window29) = true ∧ cover (Data.window30.headD 0) Data.window29 = true := by
  decide +kernel

theorem window30_ok :
    (allR isPrime Data.window30 && incr Data.window30) = true ∧ cover (Data.window31.headD 0) Data.window30 = true := by
  decide +kernel

theorem window31_ok :
    (allR isPrime Data.window31 && incr Data.window31) = true ∧ cover (Data.window32.headD 0) Data.window31 = true := by
  decide +kernel

theorem window32_ok :
    (allR isPrime Data.window32 && incr Data.window32) = true ∧ cover (Data.window33.headD 0) Data.window32 = true := by
  decide +kernel

theorem window33_ok :
    (allR isPrime Data.window33 && incr Data.window33) = true ∧ cover (Data.window34.headD 0) Data.window33 = true := by
  decide +kernel

theorem window34_ok :
    (allR isPrime Data.window34 && incr Data.window34) = true ∧ cover (Data.window35.headD 0) Data.window34 = true := by
  decide +kernel

theorem window35_ok :
    (allR isPrime Data.window35 && incr Data.window35) = true ∧ cover (Data.window36.headD 0) Data.window35 = true := by
  decide +kernel

theorem window36_ok :
    (allR isPrime Data.window36 && incr Data.window36) = true ∧ cover (Data.window37.headD 0) Data.window36 = true := by
  decide +kernel

theorem window37_ok :
    (allR isPrime Data.window37 && incr Data.window37) = true ∧ cover (Data.window38.headD 0) Data.window37 = true := by
  decide +kernel

theorem window38_ok :
    (allR isPrime Data.window38 && incr Data.window38) = true ∧ cover (Data.window39.headD 0) Data.window38 = true := by
  decide +kernel

theorem window39_ok :
    (allR isPrime Data.window39 && incr Data.window39) = true ∧ cover (Data.window40.headD 0) Data.window39 = true := by
  decide +kernel

theorem window40_ok :
    (allR isPrime Data.window40 && incr Data.window40) = true ∧ cover (Data.window41.headD 0) Data.window40 = true := by
  decide +kernel

theorem window41_ok :
    (allR isPrime Data.window41 && incr Data.window41) = true ∧ cover (Data.window42.headD 0) Data.window41 = true := by
  decide +kernel

theorem window42_ok :
    (allR isPrime Data.window42 && incr Data.window42) = true ∧ cover (Data.window43.headD 0) Data.window42 = true := by
  decide +kernel

theorem window43_ok :
    (allR isPrime Data.window43 && incr Data.window43) = true ∧ cover (Data.window44.headD 0) Data.window43 = true := by
  decide +kernel

theorem window44_ok :
    (allR isPrime Data.window44 && incr Data.window44) = true ∧ cover (Data.window45.headD 0) Data.window44 = true := by
  decide +kernel

theorem window45_ok :
    (allR isPrime Data.window45 && incr Data.window45) = true ∧ cover (Data.window46.headD 0) Data.window45 = true := by
  decide +kernel

theorem window46_ok :
    (allR isPrime Data.window46 && incr Data.window46) = true ∧ cover (Data.window47.headD 0) Data.window46 = true := by
  decide +kernel

theorem window47_ok :
    (allR isPrime Data.window47 && incr Data.window47) = true ∧ cover (Data.window48.headD 0) Data.window47 = true := by
  decide +kernel

theorem window48_ok :
    (allR isPrime Data.window48 && incr Data.window48) = true ∧ cover (Data.window49.headD 0) Data.window48 = true := by
  decide +kernel

theorem window49_ok :
    (allR isPrime Data.window49 && incr Data.window49) = true ∧ cover (Data.window50.headD 0) Data.window49 = true := by
  decide +kernel

theorem window50_ok :
    (allR isPrime Data.window50 && incr Data.window50) = true ∧ cover (Data.window51.headD 0) Data.window50 = true := by
  decide +kernel

theorem window51_ok :
    (allR isPrime Data.window51 && incr Data.window51) = true ∧ cover (Data.window52.headD 0) Data.window51 = true := by
  decide +kernel

theorem window52_ok :
    (allR isPrime Data.window52 && incr Data.window52) = true ∧ cover (Data.window53.headD 0) Data.window52 = true := by
  decide +kernel

theorem window53_ok :
    (allR isPrime Data.window53 && incr Data.window53) = true ∧ cover (Data.window54.headD 0) Data.window53 = true := by
  decide +kernel

theorem window54_ok :
    (allR isPrime Data.window54 && incr Data.window54) = true ∧ cover (Data.window55.headD 0) Data.window54 = true := by
  decide +kernel

theorem window55_ok :
    (allR isPrime Data.window55 && incr Data.window55) = true ∧ cover (Data.window56.headD 0) Data.window55 = true := by
  decide +kernel

theorem window56_ok :
    (allR isPrime Data.window56 && incr Data.window56) = true ∧ cover (Data.window57.headD 0) Data.window56 = true := by
  decide +kernel

theorem window57_ok :
    (allR isPrime Data.window57 && incr Data.window57) = true ∧ cover (Data.window58.headD 0) Data.window57 = true := by
  decide +kernel

theorem window58_ok :
    (allR isPrime Data.window58 && incr Data.window58) = true ∧ cover (Data.window59.headD 0) Data.window58 = true := by
  decide +kernel

theorem window59_ok :
    (allR isPrime Data.window59 && incr Data.window59) = true ∧ cover (Data.window60.headD 0) Data.window59 = true := by
  decide +kernel

theorem window60_ok :
    (allR isPrime Data.window60 && incr Data.window60) = true ∧ cover (Data.window61.headD 0) Data.window60 = true := by
  decide +kernel

theorem window61_ok :
    (allR isPrime Data.window61 && incr Data.window61) = true ∧ cover (Data.window62.headD 0) Data.window61 = true := by
  decide +kernel

theorem window62_ok :
    (allR isPrime Data.window62 && incr Data.window62) = true ∧ cover (Data.window63.headD 0) Data.window62 = true := by
  decide +kernel

theorem window63_ok :
    (allR isPrime Data.window63 && incr Data.window63) = true ∧ cover (Data.window64.headD 0) Data.window63 = true := by
  decide +kernel

theorem window64_ok :
    (allR isPrime Data.window64 && incr Data.window64) = true ∧ cover (Data.window65.headD 0) Data.window64 = true := by
  decide +kernel

theorem window65_ok :
    (allR isPrime Data.window65 && incr Data.window65) = true ∧ cover (Data.window66.headD 0) Data.window65 = true := by
  decide +kernel

theorem window66_ok :
    (allR isPrime Data.window66 && incr Data.window66) = true ∧ cover (Data.window67.headD 0) Data.window66 = true := by
  decide +kernel

theorem window67_ok :
    (allR isPrime Data.window67 && incr Data.window67) = true ∧ cover (Data.window68.headD 0) Data.window67 = true := by
  decide +kernel

theorem window68_ok :
    (allR isPrime Data.window68 && incr Data.window68) = true ∧ cover (4000000) Data.window68 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem windows_eq : Data.windows = [Data.window0, Data.window1, Data.window2, Data.window3, Data.window4, Data.window5, Data.window6, Data.window7, Data.window8, Data.window9, Data.window10, Data.window11, Data.window12, Data.window13, Data.window14, Data.window15, Data.window16, Data.window17, Data.window18, Data.window19, Data.window20, Data.window21, Data.window22, Data.window23, Data.window24, Data.window25, Data.window26, Data.window27, Data.window28, Data.window29, Data.window30, Data.window31, Data.window32, Data.window33, Data.window34, Data.window35, Data.window36, Data.window37, Data.window38, Data.window39, Data.window40, Data.window41, Data.window42, Data.window43, Data.window44, Data.window45, Data.window46, Data.window47, Data.window48, Data.window49, Data.window50, Data.window51, Data.window52, Data.window53, Data.window54, Data.window55, Data.window56, Data.window57, Data.window58, Data.window59, Data.window60, Data.window61, Data.window62, Data.window63, Data.window64, Data.window65, Data.window66, Data.window67, Data.window68] := rfl

theorem windows_ok : ∀ b ∈ Data.windows, allR isPrime b = true ∧ incr b = true := by
  intro b hb
  rw [windows_eq] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.and_eq_true _ _ ▸ (window0_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window1_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window2_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window3_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window4_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window5_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window6_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window7_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window8_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window9_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window10_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window11_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window12_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window13_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window14_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window15_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window16_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window17_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window18_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window19_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window20_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window21_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window22_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window23_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window24_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window25_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window26_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window27_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window28_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window29_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window30_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window31_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window32_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window33_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window34_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window35_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window36_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window37_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window38_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window39_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window40_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window41_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window42_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window43_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window44_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window45_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window46_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window47_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window48_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window49_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window50_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window51_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window52_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window53_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window54_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window55_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window56_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window57_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window58_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window59_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window60_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window61_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window62_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window63_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window64_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window65_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window66_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window67_ok).1
  · exact Bool.and_eq_true _ _ ▸ (window68_ok).1

set_option maxRecDepth 100000 in
theorem windows_cover : coverAll Data.windows = true := by
  rw [windows_eq]
  simp only [coverAll, Bool.and_eq_true]
  exact ⟨window0_ok.2, window1_ok.2, window2_ok.2, window3_ok.2, window4_ok.2, window5_ok.2, window6_ok.2, window7_ok.2, window8_ok.2, window9_ok.2, window10_ok.2, window11_ok.2, window12_ok.2, window13_ok.2, window14_ok.2, window15_ok.2, window16_ok.2, window17_ok.2, window18_ok.2, window19_ok.2, window20_ok.2, window21_ok.2, window22_ok.2, window23_ok.2, window24_ok.2, window25_ok.2, window26_ok.2, window27_ok.2, window28_ok.2, window29_ok.2, window30_ok.2, window31_ok.2, window32_ok.2, window33_ok.2, window34_ok.2, window35_ok.2, window36_ok.2, window37_ok.2, window38_ok.2, window39_ok.2, window40_ok.2, window41_ok.2, window42_ok.2, window43_ok.2, window44_ok.2, window45_ok.2, window46_ok.2, window47_ok.2, window48_ok.2, window49_ok.2, window50_ok.2, window51_ok.2, window52_ok.2, window53_ok.2, window54_ok.2, window55_ok.2, window56_ok.2, window57_ok.2, window58_ok.2, window59_ok.2, window60_ok.2, window61_ok.2, window62_ok.2, window63_ok.2, window64_ok.2, window65_ok.2, window66_ok.2, window67_ok.2, window68_ok.2⟩

theorem windows_head : (Data.windows.headD []).headD 0 = 9973 := by decide +kernel

theorem hasWindow {s : ℕ} (h1 : 9973 ≤ s) (h2 : s < 4000000) : HasWindow s := by
  refine coverAll_sound Data.windows windows_cover ?_ ?_ s ?_ h2
  · intro b hb
    exact pairwise_of_incr (windows_ok b hb).2
  · intro b hb p hp
    exact prime_of_isPrime (pairwise_of_incr trial_incr) (allR_eq_true.mp (windows_ok b hb).1 p hp)
  · have hh := windows_head
    cases hW : Data.windows with
    | nil => rw [hW] at hh; simp at hh
    | cons b bs =>
      rw [hW] at hh
      cases hb : b with
      | nil => rw [hb] at hh; simp at hh
      | cons r rs =>
        rw [hb] at hh
        simp at hh
        exact ⟨r :: rs, by simp, r, by simp, by omega⟩

end KellnerBernoulli
