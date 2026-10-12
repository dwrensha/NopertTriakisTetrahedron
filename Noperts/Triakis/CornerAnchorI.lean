module

public import Noperts.Triakis.CornerKernelPacked

@[expose] public section

/-!
# Fact boxes as integers

An anchored fact's box must contain the integer frame `X / D ± H / D`.  With the fact's box
written over a common denominator `L` (center `C / L`, radius `R / L`), containment is
`|Xᵢ L - Cᵢ D| + Hᵢ L ≤ Rᵢ D` in each coordinate: integer arithmetic only, where the
rational form normalizes every intermediate result.
-/

namespace Noperts.Triakis.CornerKernel

open CornerCertificate

/-- A fact's box over a common denominator: center `C / L`, radius `R / L`. -/
structure FBox where
  L : ℕ
  C : List ℤ
  R : List ℤ
  ok : Bool
deriving DecidableEq, Inhabited

def lcmDen (qs : List ℚ) : ℕ := qs.foldr (fun q a => Nat.lcm q.den a) 1

def scaleQ (L : ℕ) (q : ℚ) : ℤ := q.num * ((L / q.den : ℕ) : ℤ)

def mkFBox (r : Row) : FBox :=
  let cs := (List.range 7).map r.box.center
  let rs := (List.range 7).map r.box.radius
  let L := lcmDen (cs ++ rs)
  ⟨L, cs.map (scaleQ L), rs.map (scaleQ L),
    decide (r.center.length ≤ 7 ∧ r.radius.length ≤ 7)⟩

/-- `|x L - c D| + h L ≤ r D` over the coordinates, by `List.rec`. -/
def inBoxR (L D : ℕ) : List ℤ → List ℤ → List ℤ → List ℤ → Bool :=
  @List.rec ℤ (fun _ => List ℤ → List ℤ → List ℤ → Bool) (fun _ _ _ => true)
    (fun c _ ih xs hs rs =>
      decide (|xs.headD 0 * (L : ℤ) - c * (D : ℤ)| + hs.headD 0 * (L : ℤ) ≤ rs.headD 0 * (D : ℤ)) &&
        ih xs.tail hs.tail rs.tail)

def inBoxI (fb : FBox) (D : ℕ) (X H : List ℤ) : Bool :=
  fb.ok && Nat.blt 0 fb.L && inBoxR fb.L D fb.C X H fb.R

/-! ## Soundness -/

theorem lcmDen_dvd : ∀ (qs : List ℚ) (q : ℚ), q ∈ qs → q.den ∣ lcmDen qs
  | [], _, h => absurd h List.not_mem_nil
  | a :: l, q, h => by
      simp only [lcmDen, List.foldr_cons] at *
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.dvd_lcm_left _ _
      · exact (lcmDen_dvd l q h).trans (Nat.dvd_lcm_right _ _)

theorem scaleQ_cast (L : ℕ) (q : ℚ) (h : q.den ∣ L) : (scaleQ L q : ℚ) = L * q := by
  obtain ⟨m, rfl⟩ := h
  simp only [scaleQ, Nat.mul_div_cancel_left m q.den_pos]
  push_cast
  rw [← Rat.mul_den_eq_num q]
  ring

theorem inBoxR_spec (L D : ℕ) : ∀ (C X H R : List ℤ), inBoxR L D C X H R = true →
    ∀ i < C.length, |X.getD i 0 * (L : ℤ) - C.getD i 0 * (D : ℤ)| + H.getD i 0 * (L : ℤ) ≤
      R.getD i 0 * (D : ℤ)
  | [], _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | c :: C, X, H, R, h, i, hi => by
      have h' : decide (|X.headD 0 * (L : ℤ) - c * (D : ℤ)| + H.headD 0 * (L : ℤ) ≤
          R.headD 0 * (D : ℤ)) = true ∧ inBoxR L D C X.tail H.tail R.tail = true := by
        simpa [inBoxR] using h
      cases i with
      | zero =>
          have := of_decide_eq_true h'.1
          cases X <;> cases H <;> cases R <;> simpa using this
      | succ i =>
          have := inBoxR_spec L D C X.tail H.tail R.tail h'.2 i (by simpa using hi)
          cases X <;> cases H <;> cases R <;> simpa using this

/-- What an anchor needs: the integer frame's box, coordinatewise inside the fact's box. -/
theorem inBoxI_sound (r : Row) (D : ℕ) (hD : 0 < D) (X H : List ℤ)
    (h : inBoxI (mkFBox r) D X H = true) :
    r.center.length ≤ 7 ∧ r.radius.length ≤ 7 ∧ ∀ i < 7,
      |(X.getD i 0 : ℚ) / D - r.box.center i| + (H.getD i 0 : ℚ) / D ≤ r.box.radius i := by
  simp only [inBoxI, mkFBox, Bool.and_eq_true, decide_eq_true_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨hc, hr⟩, hL⟩, hb⟩ := h
  refine ⟨hc, hr, fun i hi => ?_⟩
  set L := lcmDen (((List.range 7).map r.box.center) ++ ((List.range 7).map r.box.radius))
  have hspec := inBoxR_spec L D _ X H _ hb i (by simpa using hi)
  have gc : ((List.range 7).map r.box.center |>.map (scaleQ L)).getD i 0 =
      scaleQ L (r.box.center i) := by
    simp [List.getD_eq_getElem?_getD, hi]
  have gr : ((List.range 7).map r.box.radius |>.map (scaleQ L)).getD i 0 =
      scaleQ L (r.box.radius i) := by
    simp [List.getD_eq_getElem?_getD, hi]
  rw [gc, gr] at hspec
  have dc : (r.box.center i).den ∣ L :=
    lcmDen_dvd _ _ (List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
  have dr : (r.box.radius i).den ∣ L :=
    lcmDen_dvd _ _ (List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
  have hq : (|(X.getD i 0 : ℚ) * L - scaleQ L (r.box.center i) * D| +
      (H.getD i 0 : ℚ) * L ≤ scaleQ L (r.box.radius i) * D) := by exact_mod_cast hspec
  rw [scaleQ_cast L _ dc, scaleQ_cast L _ dr] at hq
  have hLq : (0 : ℚ) < L := by exact_mod_cast hL
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have key : |(X.getD i 0 : ℚ) / D - r.box.center i| * (L * D) + (H.getD i 0 : ℚ) / D * (L * D) ≤
      r.box.radius i * (L * D) := by
    have e1 : |(X.getD i 0 : ℚ) / D - r.box.center i| * (L * D) =
        |(X.getD i 0 : ℚ) * L - L * r.box.center i * D| := by
      rw [show (X.getD i 0 : ℚ) * L - L * r.box.center i * D =
          ((X.getD i 0 : ℚ) / D - r.box.center i) * (L * D) by field_simp,
        abs_mul, abs_of_pos (by positivity : (0 : ℚ) < L * D)]
    have e2 : (H.getD i 0 : ℚ) / D * (L * D) = (H.getD i 0 : ℚ) * L := by field_simp
    rw [e1, e2]
    linarith
  have := le_of_mul_le_mul_right (by linarith : (|(X.getD i 0 : ℚ) / D - r.box.center i| +
    (H.getD i 0 : ℚ) / D) * (L * D) ≤ r.box.radius i * (L * D)) (by positivity)
  exact this

end Noperts.Triakis.CornerKernel
