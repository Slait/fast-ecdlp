import ECDLPv2.L132_Ora
import ECDLPv2.L115_Top
import ECDLP.L78_Len
import ECDLP.L77_Cap

/-!
# W1S / Count15 integration: frame, zero-test conversion, and gated ZSpecAt

The Count15 engine writes the little-endian encoding of Zc to array 2.
This file turns that output into L70's ESpec convention (scalar 3 is 1 iff
the count is zero), proves the Keep frame required by L61, and uses the
existing L77 length wrapper to obtain ZSpecAt Gx.

All claims below are Lean theorems; no axioms or sorry are introduced.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

noncomputable section
namespace ECDLP.L132

open ECDLP ECDLP.L61 ECDLP.L70 ECDLP.L77 ECDLP.L78 ECDLP.L80
  ECDLP.L85B ECDLP.L92 ECDLP.L113 ECDLP.L115
  Factoring.Aux Factoring.Aux.Copied Factoring.Aux.Copied.PLib
  Factoring.Aux.Ex Computability

theorem keep_seq {s t : Cmd} (hs : Keep s) (ht : Keep t) : Keep (.seq s t) := by
  refine ⟨?_, ?_⟩
  · intro st i hi h3
    rw [Cmd.run_seq, ht.sc _ i hi h3, hs.sc st i hi h3]
  · intro st a ha
    rw [Cmd.run_seq, ht.ar _ a ha, hs.ar st a ha]

theorem keep_loop {b c : ℕ} {body : Cmd} (hc : 10 ≤ c) (hbody : Keep body) :
    Keep (.loop b c body) := by
  refine ⟨?_, ?_⟩
  · intro st i hi h3
    apply Cmd.loop_inv (b := b) (c := c) (body := body) (st := st)
      (fun _ s => s.sc i = st.sc i) rfl
    intro j s _ hs
    have h := hbody.sc (s.setSc c j) i hi h3
    rw [h]
    simp [St.setSc_sc, Function.update_of_ne (show i ≠ c by omega), hs]
  · intro st a ha
    apply Cmd.loop_inv (b := b) (c := c) (body := body) (st := st)
      (fun _ s => s.ar a = st.ar a) rfl
    intro j s _ hs
    have h := hbody.ar (s.setSc c j) a ha
    rw [h]
    simp [St.setSc_ar, hs]

theorem keep_ifZero {x : ℕ} {s t : Cmd} (hs : Keep s) (ht : Keep t) :
    Keep (.ifZero x s t) := by
  refine ⟨?_, ?_⟩
  · intro st i hi h3
    rw [Cmd.run_ifZero]
    split_ifs
    · exact hs.sc st i hi h3
    · exact ht.sc st i hi h3
  · intro st a ha
    rw [Cmd.run_ifZero]
    split_ifs
    · exact hs.ar st a ha
    · exact ht.ar st a ha

theorem keep_ifLt {x y : ℕ} {s t : Cmd} (hs : Keep s) (ht : Keep t) :
    Keep (.ifLt x y s t) := by
  refine ⟨?_, ?_⟩
  · intro st i hi h3
    rw [Cmd.run_ifLt]
    split_ifs
    · exact hs.sc st i hi h3
    · exact ht.sc st i hi h3
  · intro st a ha
    rw [Cmd.run_ifLt]
    split_ifs
    · exact hs.ar st a ha
    · exact ht.ar st a ha

theorem keep_setK {x k : ℕ} (hx : 10 ≤ x ∨ x = 3) : Keep (.setK x k) := by
  refine ⟨?_, ?_⟩
  · intro st i hi h3
    have hix : i ≠ x := by omega
    simp [Cmd.run_setK, St.setSc_sc, Function.update_of_ne hix]
  · intro st a ha
    rfl

theorem keep_copy {x y : ℕ} (hx : 10 ≤ x ∨ x = 3) : Keep (.copy x y) := by
  refine ⟨?_, ?_⟩
  · intro st i hi h3
    have hix : i ≠ x := by omega
    simp [Cmd.run_copy, St.setSc_sc, Function.update_of_ne hix]
  · intro st a ha
    rfl

theorem keep_incr {x : ℕ} (hx : 10 ≤ x ∨ x = 3) : Keep (.incr x) := by
  refine ⟨?_, ?_⟩
  · intro st i hi h3
    have hix : i ≠ x := by omega
    simp [Cmd.run_incr, St.setSc_sc, Function.update_of_ne hix]
  · intro st a ha
    rfl

theorem keep_rd {x a i o : ℕ} (hx : 10 ≤ x ∨ x = 3) : Keep (.rd x a i o) := by
  refine ⟨?_, ?_⟩
  · intro st j hj h3
    have hjx : j ≠ x := by omega
    simp [Cmd.run_rd, St.setSc_sc, Function.update_of_ne hjx]
  · intro st a' ha
    rfl

theorem keep_wr {a i o y : ℕ} (ha : 2 ≤ a) : Keep (.wr a i o y) := by
  refine ⟨?_, ?_⟩
  · intro st j hj h3
    rfl
  · intro st a' ha'
    have haa : a' ≠ a := by omega
    simp [Cmd.run_wr, St.setAr, St.putAr, Function.update_of_ne haa]

theorem keep_of_writeSet (c : Cmd)
    (hsc : ∀ i, i < 10 → i ≠ 3 → i ∉ c.wsc)
    (har : ∀ a, a < 2 → a ∉ c.war) : Keep c :=
  ⟨fun st i hi h3 => Cmd.run_sc_frame c st i (hsc i hi h3),
   fun st a ha => Cmd.run_ar_frame c st a (har a ha)⟩

theorem keep_of_Rng {sLo sHi aLo aHi : ℕ} {c : Cmd}
    (h : ECDLP.L80.Rng sLo sHi aLo aHi c) (hs : 10 ≤ sLo) (ha : 2 ≤ aLo) : Keep c := by
  apply keep_of_writeSet c
  · intro i hi h3 hm
    have := h.1 i hm
    omega
  · intro a ha' hm
    have := h.2 a hm
    omega

theorem keep_shift (S : ℕ) (hS : 10 ≤ S) (c : Cmd) : Keep (c.shift S) := by
  apply keep_of_writeSet
  · intro i hi h3 hm
    have h := ECDLP.L80.shift_wsc S c i hm
    omega
  · intro a ha hm
    have h := ECDLP.L80.shift_war S c a hm
    omega

theorem keep_cset {e : Ex} {d : ℕ} (hv : VB 1000 e) (hd1 : d < 1000) (hd : 10 ≤ d) :
    Keep (cset e d) := by
  have hk : Keeps (cset e d) (fun y => 10 ≤ y) := Keeps.cset hv hd1 hd
  refine ⟨?_, ?_⟩
  · intro st i hi h3
    exact (hk st).1 i (by omega) (by omega)
  · intro st a ha
    exact (hk st).2 a (by omega)

theorem keep_lenC : Keep (ECDLP.L113.lenC 2) := by
  unfold ECDLP.L113.lenC ECDLP.L113.lenBody
  apply keep_seq
  · exact keep_setK (by omega)
  · apply keep_seq
    · apply keep_loop (b := 710) (c := 841) (by omega)
      apply keep_seq
      · exact keep_rd (by omega)
      · apply keep_ifZero
        · exact ⟨by intro st i hi h3; rfl, by intro st a ha; rfl⟩
        · apply keep_seq
          · exact keep_copy (by omega)
          · exact keep_incr (by omega)
    · apply keep_seq
      · exact keep_setK (by omega)
      · exact keep_wr (by norm_num)

theorem keep_toBitsC (w : ℕ) : Keep (ECDLP.L115.toBitsC 2 w) := by
  unfold ECDLP.L115.toBitsC ECDLP.L115.toBitsBody
  apply keep_seq
  · exact keep_setK (by omega)
  · apply keep_loop (b := 710) (c := 861) (by omega)
    apply keep_seq
    · exact keep_cset (by simp [VB]) (by norm_num) (by omega)
    · apply keep_seq
      · exact keep_wr (by norm_num)
      · exact keep_cset (by simp [VB]) (by norm_num) (by omega)

theorem keep_prepC : Keep ECDLP.L115.prepC := by
  apply keep_of_writeSet ECDLP.L115.prepC
  · intro i hi h3 hm
    simp [ECDLP.L115.prepC, ECDLP.L115.sqC, Cmd.wsc] at hm
    omega
  · intro a ha hm
    simp [ECDLP.L115.prepC, ECDLP.L115.sqC, Cmd.war] at hm

theorem keep_finishC :
    Keep (ECDLP.L113.finishC 100 101 102 103 2 104 105 106 110 111) := by
  apply keep_of_writeSet (ECDLP.L113.finishC 100 101 102 103 2 104 105 106 110 111)
  · intro i hi h3 hm
    simp [ECDLP.L113.finishC, ECDLP.L113.recoverC, ECDLP.L113.crtC,
      ECDLP.L113.crtBody, ECDLP.L113.crtStep, ECDLP.L113.divC,
      ECDLP.L113.divBody, ECDLP.L113.idxC, ECDLP.L113.shiftIn,
      ECDLP.L113.cmpSub, ECDLP.L113.modBig, ECDLP.L113.modBigBody,
      ECDLP.L113.findC, ECDLP.L113.findBody, ECDLP.L113.dmCmd,
      ECDLP.L113.mulCmd, ECDLP.L113.modIn, Cmd.wsc] at hm
    omega
  · intro a ha hm
    simp [ECDLP.L113.finishC, ECDLP.L113.recoverC, ECDLP.L113.crtC,
      ECDLP.L113.crtBody, ECDLP.L113.crtStep, ECDLP.L113.divC,
      ECDLP.L113.divBody, ECDLP.L113.idxC, ECDLP.L113.shiftIn,
      ECDLP.L113.cmpSub, ECDLP.L113.modBig, ECDLP.L113.modBigBody,
      ECDLP.L113.findC, ECDLP.L113.findBody, ECDLP.L113.dmCmd,
      ECDLP.L113.mulCmd, ECDLP.L113.modIn, Cmd.war] at hm
    omega

theorem keep_swpBody (S RN RD : ℕ) (U : ECDLP.L115.UParts)
    (hS : 10 ≤ S) (hRN : 2 ≤ RN) (hRD : 2 ≤ RD) :
    Keep (ECDLP.L115.swpBody S RN RD U) := by
  unfold ECDLP.L115.swpBody
  apply keep_seq
  · exact keep_copy (by omega)
  · apply keep_seq
    · exact keep_shift S hS (ECDLP.L115.modBodyR U)
    · apply keep_seq
      · exact keep_wr hRN
      · exact keep_wr hRD

theorem keep_swpC (S RN RD : ℕ) (U : ECDLP.L115.UParts)
    (hS : 10 ≤ S) (hRN : 2 ≤ RN) (hRD : 2 ≤ RD) :
    Keep (ECDLP.L115.swpC S RN RD U) := by
  unfold ECDLP.L115.swpC
  apply keep_seq
  · exact keep_shift S hS (ECDLP.L115.setup U)
  · apply keep_seq
    · exact keep_shift S hS (cset ECDLP.L115.mE 314)
    · apply keep_seq
      · exact keep_copy (by omega)
      · exact keep_loop (b := 852) (c := 851) (by omega)
          (keep_swpBody S RN RD U hS hRN hRD)

theorem keep_longC (S RN RD : ℕ) (U : ECDLP.L115.UParts)
    (X1 X2 Pa T Q R TM ONE : ℕ) (hS : 10 ≤ S) (hRN : 2 ≤ RN) (hRD : 2 ≤ RD)
    (hQ : 2 ≤ Q) (hX1 : 2 ≤ X1) (hX2 : 2 ≤ X2) (hP : 2 ≤ Pa) (hT : 2 ≤ T)
    (hR : 2 ≤ R) (hTM : 2 ≤ TM) (hONE : 2 ≤ ONE) :
    Keep (ECDLP.L115.longC S RN RD U X1 X2 Pa T Q R TM ONE) := by
  unfold ECDLP.L115.longC
  exact keep_seq (keep_swpC S RN RD U hS hRN hRD)
    (keep_seq keep_prepC keep_finishC)

theorem keep_cntShort (r S : ℕ) (hS : 10 ≤ S) : Keep (ECDLP.L132.cntShort r S) := by
  unfold ECDLP.L132.cntShort ECDLP.L132.cntShortG
  apply keep_seq
  · exact keep_shift S hS (ECDLP.L115.lookCnt (r + 1) (ECDLP.L115.T1 r))
  · apply keep_seq
    · exact keep_copy (by omega)
    · apply keep_seq
      · exact keep_toBitsC (r * ECDLP.L115.T1 r + 1)
      · exact keep_lenC

theorem keep_cntLong (r S : ℕ) (hS : 10 ≤ S) :
    Keep (ECDLP.L132.cntLong r S) := by
  unfold ECDLP.L132.cntLong
  exact keep_longC S 110 111 (ECDLP.L115.realU r) 100 101 102 103 2 104 105 106
    hS (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem keep_cntBr (r S : ℕ) (hS : 10 ≤ S) : Keep (ECDLP.L132.cntBr r S) := by
  unfold ECDLP.L132.cntBr
  apply keep_seq
  · exact keep_setK (by omega)
  · exact keep_ifLt (keep_cntShort r S hS) (keep_cntLong r S hS)

theorem keep_cntOra (r S : ℕ) (hS : 1400 ≤ S) : Keep (ECDLP.L132.cntOra r S) := by
  unfold ECDLP.L132.cntOra
  apply keep_seq
  · exact keep_of_Rng (ECDLP.L80.checkC_rng (r + 1)) (by omega) (by omega)
  · apply keep_seq
    · exact keep_of_Rng (ECDLP.L92.frameW'_rng S hS) (by omega) (by omega)
    · exact keep_cntBr r S (by omega)

/-- The Count15 output length is converted to the zero-test flag required by ESpec. -/
def cntZeroFlag : Cmd :=
  .seq (.setK 843 0)
    (.seq (.rd 860 2 843 0)
      (.ifZero 860 (.setK 3 1) (.setK 3 0)))

theorem cntZeroFlag_run (st : St) :
    (Cmd.run cntZeroFlag st).1.sc 3 = (if st.ar 2 0 = 0 then 1 else 0) ∧
    (Cmd.run cntZeroFlag st).2 = 6 := by
  simp [cntZeroFlag, Cmd.run_seq, Cmd.run_setK, Cmd.run_rd, Cmd.run_ifZero,
    St.setSc_sc, Function.update_apply]

theorem keep_cntZeroFlag : Keep cntZeroFlag := by
  unfold cntZeroFlag
  apply keep_seq
  · exact keep_setK (by omega)
  · apply keep_seq
    · exact keep_rd (by omega)
    · exact keep_ifZero (keep_setK (by omega)) (keep_setK (by omega))

theorem outOf_length (μ : ℕ → ℕ) : (outOf μ).length = μ 0 := by
  simp [outOf]

theorem encodeNat_eq_nil_iff (n : ℕ) : encodeNat n = [] ↔ n = 0 := by
  constructor
  · intro h
    have h' : encodeNat n = encodeNat 0 := by
      simpa [ECDLP.L115.encodeNat_zero] using h
    exact ECDLP.L61.encodeNat_inj h'
  · rintro rfl
    exact ECDLP.L115.encodeNat_zero

theorem cntOra_ESpec (S : ℕ) (hS : 1400 ≤ S) :
    ∃ Tc : ℕ → ℕ,
      ESpec 15 (Cmd.seq (cntOra 14 S) cntZeroFlag) (fun L => Tc L + 7) ∧
      (∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, Tc L ≤ C * 2 ^ (L / k)) := by
  obtain ⟨Tc, hval, hT⟩ := cntOra_spec 14 (by norm_num) S hS
  refine ⟨Tc, ?_, hT⟩
  refine ⟨keep_seq (keep_cntOra 14 S hS) keep_cntZeroFlag, ?_⟩
  intro x st τ hconf hok hgood
  obtain ⟨hcount, hcost⟩ := hval x st τ hconf hgood
  set q := (Cmd.run (cntOra 14 S) st).1
  have hcell : q.ar 2 0 = (encodeNat (Zc 15 x τ)).length := by
    have hlen := outOf_length (q.ar 2)
    calc
      q.ar 2 0 = (outOf (q.ar 2)).length := hlen.symm
      _ = (encodeNat (Zc 15 x τ)).length := by rw [hcount]
  have hzero : q.ar 2 0 = 0 ↔ Zc 15 x τ = 0 := by
    rw [hcell]
    constructor
    · intro h
      exact (encodeNat_eq_nil_iff (Zc 15 x τ)).mp (List.length_eq_zero_iff.mp h)
    · intro h
      rw [h, ECDLP.L115.encodeNat_zero]
      rfl
  have hf := cntZeroFlag_run q
  have hrun : Cmd.run (Cmd.seq (cntOra 14 S) cntZeroFlag) st =
      ((Cmd.run cntZeroFlag q).1,
        (Cmd.run (cntOra 14 S) st).2 + (Cmd.run cntZeroFlag q).2 + 1) := by
    simp only [Cmd.run_seq, q]
  refine ⟨?_, ?_⟩
  · rw [hrun, hf.1]
    by_cases hz : Zc 15 x τ = 0
    · have hq : q.ar 2 0 = 0 := hzero.mpr hz
      simp [hq, hz]
    · have hq : q.ar 2 0 ≠ 0 := fun h => hz (hzero.mp h)
      have hp : 0 < Zc 15 x τ := Nat.pos_of_ne_zero hz
      simp [hq, hp]
  · rw [hrun, hf.2]
    omega

theorem cntOra_zspecAt (S : ℕ) (hS : 1400 ≤ S) :
    ∃ T : ℕ → ℕ,
      ZSpecAt Gx 15 (wrapCmd (lenCmd 15) (Cmd.seq (cntOra 14 S) cntZeroFlag))
        (fun L => Tl 15 L + (T L + 7) + 6) ∧
      (∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ L, T L ≤ C * 2 ^ (L / k)) := by
  obtain ⟨T, hE, hT⟩ := cntOra_ESpec S hS
  refine ⟨T, ?_, hT⟩
  exact zspecAt_of_wrap (lspec_len 15 (by norm_num)) hE

end ECDLP.L132
end
