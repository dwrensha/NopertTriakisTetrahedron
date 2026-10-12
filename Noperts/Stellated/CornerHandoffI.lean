module

public import Noperts.Stellated.CornerKernelTree
public import Noperts.Stellated.CornerCoverage

@[expose] public section

/-!
# Hand-offs on integer frames

The pocket hand-offs (`pocket`, `spocket`, `ppocket`) only bound the coordinates of the frame.
On an integer frame (center `X / D`, radius `H / D`) each bound is one integer comparison:
`q ≤ (Xᵢ - Hᵢ) / D` iff `q.num · D ≤ (Xᵢ - Hᵢ) · q.den`.  `handoffI` checks them so, without
building the rational frame `IFrame.toFrame`; `stageI_sound` relates it to the stage.
-/

namespace Noperts.Stellated.CornerKernel

open CornerTree CornerHandoff CornerCertificate

/-- `q ≤ lo i`. -/
def IFrame.loGe (f : IFrame) (i : ℕ) (q : ℚ) : Bool :=
  decide (q.num * (f.D : ℤ) ≤ (f.X.getD i 0 - f.H.getD i 0) * q.den)

/-- `hi i ≤ q`. -/
def IFrame.hiLe (f : IFrame) (i : ℕ) (q : ℚ) : Bool :=
  decide ((f.X.getD i 0 + f.H.getD i 0) * q.den ≤ q.num * f.D)

/-- `lo i = q`. -/
def IFrame.loEq (f : IFrame) (i : ℕ) (q : ℚ) : Bool :=
  decide ((f.X.getD i 0 - f.H.getD i 0) * q.den = q.num * f.D)

/-- `hi i = q`. -/
def IFrame.hiEq (f : IFrame) (i : ℕ) (q : ℚ) : Bool :=
  decide ((f.X.getD i 0 + f.H.getD i 0) * q.den = q.num * f.D)

/-- `q ≤ a / D` from `q.num · D ≤ a · q.den`. -/
theorem le_div_of_cross (q : ℚ) (a : ℤ) (D : ℕ) (hD : 0 < D)
    (h : q.num * (D : ℤ) ≤ a * q.den) : q ≤ (a : ℚ) / D := by
  have hq : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hD' : (0 : ℚ) < D := by exact_mod_cast hD
  rw [le_div_iff₀ hD', ← Rat.num_div_den q, div_mul_eq_mul_div, div_le_iff₀ hq]
  exact_mod_cast h

theorem div_le_of_cross (q : ℚ) (a : ℤ) (D : ℕ) (hD : 0 < D)
    (h : a * q.den ≤ q.num * (D : ℤ)) : (a : ℚ) / D ≤ q := by
  have hq : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hD' : (0 : ℚ) < D := by exact_mod_cast hD
  rw [div_le_iff₀ hD', ← Rat.num_div_den q, div_mul_eq_mul_div, le_div_iff₀ hq]
  exact_mod_cast h

theorem div_eq_of_cross (q : ℚ) (a : ℤ) (D : ℕ) (hD : 0 < D)
    (h : a * q.den = q.num * (D : ℤ)) : (a : ℚ) / D = q :=
  le_antisymm (div_le_of_cross q a D hD h.le) (le_div_of_cross q a D hD h.ge)

section
variable (f : IFrame) (hg : f.Good)
include hg

theorem IFrame.toFrame_lo (i : ℕ) :
    f.toFrame.lo i = ((f.X.getD i 0 - f.H.getD i 0 : ℤ) : ℚ) / f.D := by
  simp only [Frame.lo, Frame.toRow, Row.lo, Row.box, IFrame.toFrame, f.getD_Xq, f.getD_Hq hg]
  push_cast
  ring

theorem IFrame.toFrame_hi (i : ℕ) :
    f.toFrame.hi i = ((f.X.getD i 0 + f.H.getD i 0 : ℤ) : ℚ) / f.D := by
  simp only [Frame.hi, Frame.toRow, Row.hi, Row.box, IFrame.toFrame, f.getD_Xq, f.getD_Hq hg]
  push_cast
  ring

theorem IFrame.loGe_sound {i : ℕ} {q : ℚ} (h : f.loGe i q = true) : q ≤ f.toFrame.lo i := by
  rw [f.toFrame_lo hg]
  exact le_div_of_cross q _ _ hg.D (by simpa [IFrame.loGe] using h)

theorem IFrame.hiLe_sound {i : ℕ} {q : ℚ} (h : f.hiLe i q = true) : f.toFrame.hi i ≤ q := by
  rw [f.toFrame_hi hg]
  exact div_le_of_cross q _ _ hg.D (by simpa [IFrame.hiLe] using h)

theorem IFrame.loEq_sound {i : ℕ} {q : ℚ} (h : f.loEq i q = true) : f.toFrame.lo i = q := by
  rw [f.toFrame_lo hg]
  exact div_eq_of_cross q _ _ hg.D (by simpa [IFrame.loEq] using h)

theorem IFrame.hiEq_sound {i : ℕ} {q : ℚ} (h : f.hiEq i q = true) : f.toFrame.hi i = q := by
  rw [f.toFrame_hi hg]
  exact div_eq_of_cross q _ _ hg.D (by simpa [IFrame.hiEq] using h)

end

/-- The pocket-family hand-offs, by integer comparisons (others: `false`). -/
def handoffI (e0 : ℚ) : Handoff → IFrame → Bool
  | .ppocket, f =>
      let pk := fun (k : Fin 3) =>
        ((ppocketSpec k).1 == f.seg) && f.loGe 2 (ppocketSpec k).2.1 &&
          f.hiLe 2 (ppocketSpec k).2.2.1 && f.loGe 5 ((ppocketSpec k).2.2.2 - 31 / 64) &&
          f.hiLe 5 ((ppocketSpec k).2.2.2 + 31 / 64)
      decide (f.kind = .plain) && Nat.beq f.X.length 6 && f.loEq 1 1 && f.hiEq 1 1 &&
        f.loGe 0 0 && f.hiLe 0 e0 && f.loGe 3 (-pocketW) && f.hiLe 3 pocketW &&
        f.loGe 4 0 && f.hiLe 4 1 && (pk 0 || pk 1 || pk 2)
  | .pocket, f =>
      let pk := fun (k : Fin 3) =>
        ((pocketSpec k).1 == f.seg) && f.loGe 2 (pocketSpec k).2.2.1 &&
          f.hiLe 2 (pocketSpec k).2.2.2 && f.loEq 5 (faceSign (pocketSpec k).2.1.val) &&
          f.hiEq 5 (faceSign (pocketSpec k).2.1.val)
      decide (f.kind = .tube) && Nat.beq f.X.length 7 && f.loEq 1 1 && f.hiEq 1 1 &&
        f.loGe 0 0 && f.hiLe 0 e0 && f.loGe 3 (-pocketW) && f.hiLe 3 pocketW &&
        f.loGe 4 pocketB0 && f.hiLe 4 pocketB1 && f.loGe 6 0 && f.hiLe 6 rho0 &&
        (pk 0 || pk 1 || pk 2)
  | .spocket, f =>
      decide (f.kind = .skew) && (f.seg == true) && Nat.beq f.X.length 6 && f.loEq 1 1 &&
        f.hiEq 1 1 && f.loGe 0 0 && f.hiLe 0 e0 && f.loGe 2 0 && f.hiLe 2 1 &&
        f.loGe 3 (-pocketW) && f.hiLe 3 pocketW && f.loGe 4 skewB0 && f.hiLe 4 skewB1 &&
        f.loGe 5 (-skewDelta) && f.hiLe 5 skewDelta
  | _, _ => false

theorem handoffI_sound (e0 : ℚ) (h : Handoff) (f : IFrame) (hg : f.Good)
    (hI : handoffI e0 h f = true) : HandoffValid e0 h f.toFrame := by
  have hlen : f.toFrame.center.length = f.X.length ∧ f.toFrame.radius.length = f.X.length := by
    simp [IFrame.toFrame]
  cases h <;> simp only [handoffI, Bool.false_eq_true] at hI
  · -- pocket
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Nat.beq_eq,
      beq_iff_eq, and_assoc] at hI
    obtain ⟨hk, hl, l1, h1, l0, h0, l3, h3, l4, h4, l6, h6, hpk⟩ := hI
    refine ⟨hk, rfl, by rw [hlen.1, hl], by rw [hlen.2, hl], f.loEq_sound hg l1,
      f.hiEq_sound hg h1, f.loGe_sound hg l0, f.hiLe_sound hg h0, f.loGe_sound hg l3,
      f.hiLe_sound hg h3, f.loGe_sound hg l4, f.hiLe_sound hg h4, f.loGe_sound hg l6,
      f.hiLe_sound hg h6, ?_⟩
    rcases hpk with (hp | hp) | hp
    all_goals
      obtain ⟨hs, a, b, c, d⟩ := hp
      exact ⟨_, hs, f.loGe_sound hg a, f.hiLe_sound hg b, f.loEq_sound hg c, f.hiEq_sound hg d⟩
  · -- spocket
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.beq_eq, beq_iff_eq, and_assoc] at hI
    obtain ⟨hk, hs, hl, l1, h1, l0, h0, l2, h2, l3, h3, l4, h4, l5, h5⟩ := hI
    exact ⟨hk, hs, rfl, by rw [hlen.1, hl], by rw [hlen.2, hl], f.loEq_sound hg l1,
      f.hiEq_sound hg h1, f.loGe_sound hg l0, f.hiLe_sound hg h0, f.loGe_sound hg l2,
      f.hiLe_sound hg h2, f.loGe_sound hg l3, f.hiLe_sound hg h3, f.loGe_sound hg l4,
      f.hiLe_sound hg h4, f.loGe_sound hg l5, f.hiLe_sound hg h5⟩
  · -- ppocket
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Nat.beq_eq,
      beq_iff_eq, and_assoc] at hI
    obtain ⟨hk, hl, l1, h1, l0, h0, l3, h3, l4, h4, hpk⟩ := hI
    refine ⟨hk, rfl, by rw [hlen.1, hl], by rw [hlen.2, hl], f.loEq_sound hg l1,
      f.hiEq_sound hg h1, f.loGe_sound hg l0, f.hiLe_sound hg h0, f.loGe_sound hg l3,
      f.hiLe_sound hg h3, f.loGe_sound hg l4, f.hiLe_sound hg h4, ?_⟩
    rcases hpk with (hp | hp) | hp
    all_goals
      obtain ⟨hs, a, b, c, d⟩ := hp
      exact ⟨_, hs, f.loGe_sound hg a, f.hiLe_sound hg b, f.loGe_sound hg c, f.hiLe_sound hg d⟩

/-- The integer hand-off check of a stage. -/
def stageI (e0 : ℚ) (allowed : Handoff → Bool) (h : Handoff) (f : IFrame) : Bool :=
  allowed h && handoffI e0 h f

theorem stageI_sound (e0 : ℚ) (allowed : Handoff → Bool) (h : Handoff) (f : IFrame)
    (hg : f.Good) (hI : stageI e0 allowed h f = true) :
    (CornerCoverage.stage e0 allowed).Valid h f.toFrame := by
  simp only [stageI, Bool.and_eq_true] at hI
  exact ⟨hI.1, handoffI_sound e0 h f hg hI.2⟩

end Noperts.Stellated.CornerKernel
