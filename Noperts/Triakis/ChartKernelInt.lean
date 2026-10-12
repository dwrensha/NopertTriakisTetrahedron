module

public import Noperts.Triakis.ChartKernelTree

@[expose] public section

/-!
# Chart trees over integer frames

`CTree.check` carries the frame as a rational interval and view triangle: every Cayley split
and view split normalizes rational midpoints, and every leaf then rescales them to integers
(`triL`, `boxE`).  `CTree.checkI` carries the same frame as integers instead: each interval
coordinate as `[lo, hi] / den`, the view triangle as three integer vertices over a common
denominator.  A split is a few integer operations; a leaf builds its rational box from the
integers (`mkRat`, one normalization per entry) and runs the unchanged leaf checkers.
`checkI_imp` reduces `checkI` to `check`, so all the leaf soundness proofs are reused.
-/

namespace Noperts.Triakis.ChartKernelTree

open CayleyAtlas AtlasProjectiveView AtlasProjectiveSolutionTree

/-- An interval coordinate `[lo, hi] / den`. -/
structure ZC where
  lo : ℤ
  hi : ℤ
  den : ℕ
deriving DecidableEq

/-- A view vertex: three numerators. -/
structure ZV where
  a : ℤ
  b : ℤ
  c : ℤ
deriving DecidableEq

/-- A region: the sphere, or a view triangle with vertices over a common denominator. -/
inductive ZR where
  | sphere
  | tri (root : Fin 8) (v0 v1 v2 : ZV) (d : ℕ)
deriving DecidableEq

/-- An integer frame: five interval coordinates and a region. -/
structure ZF where
  c0 : ZC
  c1 : ZC
  c2 : ZC
  c3 : ZC
  c4 : ZC
  reg : ZR
deriving DecidableEq

/-! ## The rational frame of an integer frame -/

def ZC.ok (c : ZC) : Bool := Nat.blt 0 c.den && decide (c.lo ≤ c.hi)

def ZF.ok (f : ZF) : Bool := f.c0.ok && f.c1.ok && f.c2.ok && f.c3.ok && f.c4.ok

def ZF.pose (f : ZF) (upper : Bool) : AtlasPose ℚ :=
  let q := fun (c : ZC) => mkRat (cond upper c.hi c.lo) c.den
  ⟨q f.c0, q f.c1, q f.c2, q f.c3, q f.c4⟩

theorem ZC.le (c : ZC) (h : c.ok = true) : mkRat c.lo c.den ≤ mkRat c.hi c.den := by
  simp only [ZC.ok, Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq] at h
  rw [Rat.mkRat_eq_div, Rat.mkRat_eq_div]
  have : (0 : ℚ) ≤ c.den := by positivity
  exact div_le_div_of_nonneg_right (by exact_mod_cast h.2) this

theorem ZF.pose_le (f : ZF) (h : f.ok = true) : f.pose false ≤ f.pose true := by
  simp only [ZF.ok, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
  rw [AtlasPose.le_iff_forall_get]
  intro i
  fin_cases i
  · exact ZC.le _ h0
  · exact ZC.le _ h1
  · exact ZC.le _ h2
  · exact ZC.le _ h3
  · exact ZC.le _ h4

/-- The rational interval of an integer frame. -/
def ZF.toInterval (f : ZF) : Interval :=
  if h : f.ok = true then AtlasInterval.mk (f.pose false) (f.pose true) (f.pose_le h)
  else AtlasPose.rootInterval ℚ

def ZV.toV (v : ZV) (d : ℕ) : Noperts.ProjectiveView.Vector ℚ :=
  fun j => match j with
    | 0 => mkRat v.a d
    | 1 => mkRat v.b d
    | 2 => mkRat v.c d

def ZR.toRegion : ZR → Region
  | .sphere => .sphere
  | .tri r v0 v1 v2 d => .triangle r (tri3K (v0.toV d) (v1.toV d) (v2.toV d))

/-! ## Integer frame operations -/

def ZC.half (c : ZC) (upper : Bool) : ZC :=
  cond upper ⟨Int.add c.lo c.hi, Int.mul 2 c.hi, Nat.mul 2 c.den⟩
    ⟨Int.mul 2 c.lo, Int.add c.lo c.hi, Nat.mul 2 c.den⟩

def ZF.half (f : ZF) (i : Fin 5) (upper : Bool) : ZF :=
  match i with
  | 0 => { f with c0 := f.c0.half upper }
  | 1 => { f with c1 := f.c1.half upper }
  | 2 => { f with c2 := f.c2.half upper }
  | 3 => { f with c3 := f.c3.half upper }
  | 4 => { f with c4 := f.c4.half upper }

def ZV.add (v w : ZV) : ZV := ⟨Int.add v.a w.a, Int.add v.b w.b, Int.add v.c w.c⟩

def ZV.dbl (v : ZV) : ZV := ⟨Int.mul 2 v.a, Int.mul 2 v.b, Int.mul 2 v.c⟩

def ZV.smul (k : ℤ) (v : ZV) : ZV := ⟨Int.mul k v.a, Int.mul k v.b, Int.mul k v.c⟩

/-- `splitK` on integer vertices (denominator doubled). -/
def splitZ (r : Fin 8) (v0 v1 v2 : ZV) (d : ℕ) (k : Fin 4) : ZR :=
  match k with
  | 0 => .tri r v0.dbl (v0.add v1) (v0.add v2) (Nat.mul 2 d)
  | 1 => .tri r (v0.add v1) v1.dbl (v1.add v2) (Nat.mul 2 d)
  | 2 => .tri r (v0.add v2) (v1.add v2) v2.dbl (Nat.mul 2 d)
  | 3 => .tri r (v0.add v1) (v1.add v2) (v2.add v0) (Nat.mul 2 d)

/-- The weights over the common denominator `E = ∏ denᵢ`. -/
def cutE (w : Fin 3 → ℚ) : ℕ := (w 0).den * (w 1).den * (w 2).den

def cutCoef (w : Fin 3 → ℚ) (j : Fin 3) : ℤ := (w j).num * ((cutE w / (w j).den : ℕ) : ℤ)

/-- `cutTriangle` on integer vertices (denominator multiplied by `cutE w`). -/
def cutZ (r : Fin 8) (v0 v1 v2 : ZV) (d : ℕ) (w : Fin 3 → ℚ) (k : Fin 3) : ZR :=
  let E : ℤ := cutE w
  let p := ((v0.smul (cutCoef w 0)).add (v1.smul (cutCoef w 1))).add (v2.smul (cutCoef w 2))
  match k with
  | 0 => .tri r p (v1.smul E) (v2.smul E) (Nat.mul d (cutE w))
  | 1 => .tri r (v0.smul E) p (v2.smul E) (Nat.mul d (cutE w))
  | 2 => .tri r (v0.smul E) (v1.smul E) p (Nat.mul d (cutE w))

/-- The chamber triangle over `6`. -/
def chamberZ : ZR := .tri 0 ⟨6, 0, 0⟩ ⟨3, 3, 0⟩ ⟨2, 2, 2⟩ 6

/-- The root interval. -/
def rootZ : ZF := ⟨⟨0, 8, 5⟩, ⟨0, 4, 1⟩, ⟨-1, 1, 1⟩, ⟨-1, 1, 1⟩, ⟨-1, 1, 1⟩, .sphere⟩

def Step.applyZ : Step → ZF → ZF
  | .half c u, f => f.half c u
  | .root, f => { f with reg := chamberZ }
  | .view k, f => match f.reg with
      | .tri r v0 v1 v2 d => { f with reg := splitZ r v0 v1 v2 d k }
      | .sphere => f
  | .cut w k, f => match f.reg with
      | .tri r v0 v1 v2 d => { f with reg := cutZ r v0 v1 v2 d w k }
      | .sphere => f

def framePathZ (steps : List Step) : ZF := steps.foldl (fun f s => s.applyZ f) rootZ

/-! ## The check -/

def CTree.checkI (hdr : Fin 64 → Option Header) (ch : ChartIndex) : ZF → CTree → Bool
  | f, .cayleySplit c lo hi =>
      CTree.checkI hdr ch (f.half c false) lo && CTree.checkI hdr ch (f.half c true) hi
  | f, .viewRoot child => CTree.checkI hdr ch { f with reg := chamberZ } child
  | f, .viewSplit c0 c1 c2 c3 =>
      match f.reg with
      | .tri r v0 v1 v2 d =>
          CTree.checkI hdr ch { f with reg := splitZ r v0 v1 v2 d 0 } c0 &&
          CTree.checkI hdr ch { f with reg := splitZ r v0 v1 v2 d 1 } c1 &&
          CTree.checkI hdr ch { f with reg := splitZ r v0 v1 v2 d 2 } c2 &&
          CTree.checkI hdr ch { f with reg := splitZ r v0 v1 v2 d 3 } c3
      | .sphere => false
  | f, .viewCut w c0 c1 c2 =>
      match f.reg with
      | .tri r v0 v1 v2 d =>
          decide ((∀ j, 0 ≤ w j) ∧ w 0 + w 1 + w 2 = 1) &&
          (!decide (0 < w 0) || CTree.checkI hdr ch { f with reg := cutZ r v0 v1 v2 d w 0 } c0) &&
          (!decide (0 < w 1) || CTree.checkI hdr ch { f with reg := cutZ r v0 v1 v2 d w 1 } c1) &&
          (!decide (0 < w 2) || CTree.checkI hdr ch { f with reg := cutZ r v0 v1 v2 d w 2 } c2)
      | .sphere => false
  | f, .octahedron => decide f.toInterval.outsideOctahedron
  | f, .hole steps => decide (framePathZ steps = f)
  | f, t =>
      match f.reg with
      | .tri r v0 v1 v2 d => leafOk hdr ch f.toInterval r (tri3K (v0.toV d) (v1.toV d) (v2.toV d)) t
      | .sphere => false

/-! ## Soundness: `checkI` simulates `check` -/

theorem iadd (a b : ℤ) : Int.add a b = a + b := rfl
theorem imul (a b : ℤ) : Int.mul a b = a * b := rfl

def ZF.coord (f : ZF) : Fin 5 → ZC
  | 0 => f.c0 | 1 => f.c1 | 2 => f.c2 | 3 => f.c3 | 4 => f.c4

theorem ZF.ok_iff (f : ZF) : f.ok = true ↔ ∀ j, (f.coord j).ok = true := by
  simp only [ZF.ok, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ j
    fin_cases j <;> assumption
  · intro h
    exact ⟨⟨⟨⟨h 0, h 1⟩, h 2⟩, h 3⟩, h 4⟩

theorem ZF.pose_get (f : ZF) (u : Bool) (j : Fin 5) :
    (f.pose u).get j = mkRat (cond u (f.coord j).hi (f.coord j).lo) (f.coord j).den := by
  fin_cases j <;> rfl

theorem ZF.half_coord (f : ZF) (i : Fin 5) (u : Bool) (j : Fin 5) :
    (f.half i u).coord j = if j = i then (f.coord i).half u else f.coord j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem ZC.half_ok (c : ZC) (u : Bool) (h : c.ok = true) : (c.half u).ok = true := by
  simp only [ZC.ok, Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq] at h ⊢
  cases u <;> simp only [ZC.half, Bool.cond_false, Bool.cond_true, iadd, imul, Nat.mul_eq] <;> omega

theorem ZF.half_ok (f : ZF) (i : Fin 5) (u : Bool) (h : f.ok = true) : (f.half i u).ok = true := by
  rw [ZF.ok_iff] at h ⊢
  intro j
  rw [ZF.half_coord]
  split
  · exact ZC.half_ok _ _ (h i)
  · exact h j

theorem AtlasPose.ext_get {p q : AtlasPose ℚ} (h : ∀ j, p.get j = q.get j) : p = q := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
  cases p; cases q
  simp only [AtlasPose.get_zero, AtlasPose.get_one, AtlasPose.get_two, AtlasPose.get_three,
    AtlasPose.get_four] at h0 h1 h2 h3 h4
  subst h0 h1 h2 h3 h4
  rfl

theorem ZF.toInterval_min (f : ZF) (h : f.ok = true) : f.toInterval.min = f.pose false := by
  simp [ZF.toInterval, h]

theorem ZF.toInterval_max (f : ZF) (h : f.ok = true) : f.toInterval.max = f.pose true := by
  simp [ZF.toInterval, h]

theorem interval_ext {a b : Interval} (h1 : a.min = b.min) (h2 : a.max = b.max) : a = b := by
  obtain ⟨⟨a1, a2⟩, ha⟩ := a
  obtain ⟨⟨b1, b2⟩, hb⟩ := b
  change a1 = b1 at h1
  change a2 = b2 at h2
  subst h1 h2
  rfl

theorem mkRat_dbl (a : ℤ) (d : ℕ) : mkRat (2 * a) (2 * d) = mkRat a d := by
  rw [Rat.mkRat_eq_div, Rat.mkRat_eq_div]
  push_cast
  ring

theorem mkRat_mid (a b : ℤ) (d : ℕ) : mkRat (a + b) (2 * d) = (mkRat a d + mkRat b d) / 2 := by
  rw [Rat.mkRat_eq_div, Rat.mkRat_eq_div, Rat.mkRat_eq_div]
  push_cast
  ring

theorem ZF.half_toInterval (f : ZF) (i : Fin 5) (u : Bool) (h : f.ok = true) :
    (f.half i u).toInterval =
      cond u (f.toInterval.upperHalf i) (f.toInterval.lowerHalf i) := by
  have h' := f.half_ok i u h
  apply interval_ext
  · rw [ZF.toInterval_min _ h']
    apply AtlasPose.ext_get
    intro j
    rw [ZF.pose_get, ZF.half_coord]
    cases u
    · simp only [Bool.cond_false, AtlasInterval.lowerHalf, AtlasInterval.min, ZF.toInterval_min _ h]
      show _ = (f.pose false).get j
      rw [ZF.pose_get]
      split
      · subst j
        simp only [ZC.half, Bool.cond_false, imul, Nat.mul_eq]
        exact mkRat_dbl _ _
      · rfl
    · simp only [Bool.cond_true, AtlasInterval.upperHalf, AtlasInterval.min]
      show _ = ((f.toInterval.min).set i (f.toInterval.midpoint i)).get j
      split
      · subst j
        rw [AtlasPose.get_set_same, AtlasInterval.midpoint, ZF.toInterval_min _ h,
          ZF.toInterval_max _ h, ZF.pose_get, ZF.pose_get]
        simp only [ZC.half, Bool.cond_true, Bool.cond_false, iadd, Nat.mul_eq]
        exact mkRat_mid _ _ _
      · rename_i hj
        rw [AtlasPose.get_set_of_ne _ _ hj, ZF.toInterval_min _ h, ZF.pose_get]
  · rw [ZF.toInterval_max _ h']
    apply AtlasPose.ext_get
    intro j
    rw [ZF.pose_get, ZF.half_coord]
    cases u
    · simp only [Bool.cond_false, AtlasInterval.lowerHalf, AtlasInterval.max]
      show _ = ((f.toInterval.max).set i (f.toInterval.midpoint i)).get j
      split
      · subst j
        rw [AtlasPose.get_set_same, AtlasInterval.midpoint, ZF.toInterval_min _ h,
          ZF.toInterval_max _ h, ZF.pose_get, ZF.pose_get]
        simp only [ZC.half, Bool.cond_true, Bool.cond_false, iadd, Nat.mul_eq]
        exact mkRat_mid _ _ _
      · rename_i hj
        rw [AtlasPose.get_set_of_ne _ _ hj, ZF.toInterval_max _ h, ZF.pose_get]
    · simp only [Bool.cond_true, AtlasInterval.upperHalf, AtlasInterval.max, ZF.toInterval_max _ h]
      show _ = (f.pose true).get j
      rw [ZF.pose_get]
      split
      · subst j
        simp only [ZC.half, Bool.cond_true, imul, Nat.mul_eq]
        exact mkRat_dbl _ _
      · rfl

theorem ZV.toV_dbl (v : ZV) (d : ℕ) : v.dbl.toV (Nat.mul 2 d) = v.toV d := by
  funext j
  fin_cases j <;> exact mkRat_dbl _ _

theorem ZV.toV_add (v w : ZV) (d : ℕ) :
    (v.add w).toV (Nat.mul 2 d) = Noperts.ProjectiveView.midpoint (v.toV d) (w.toV d) := by
  funext j
  fin_cases j <;> exact mkRat_mid _ _ _

theorem tri3K_ext {a b c a' b' c' : Noperts.ProjectiveView.Vector ℚ}
    (ha : a = a') (hb : b = b') (hc : c = c') : tri3K a b c = tri3K a' b' c' := by
  rw [ha, hb, hc]

theorem splitZ_toRegion (r : Fin 8) (v0 v1 v2 : ZV) (d : ℕ) (k : Fin 4) :
    (splitZ r v0 v1 v2 d k).toRegion =
      .triangle r (splitK (tri3K (v0.toV d) (v1.toV d) (v2.toV d)) k) := by
  fin_cases k <;> simp only [splitZ, ZR.toRegion, splitK, Region.triangle.injEq, true_and] <;>
    · apply tri3K_ext <;>
        simp only [ZV.toV_dbl, ZV.toV_add] <;> rfl

theorem cutE_pos (w : Fin 3 → ℚ) : 0 < cutE w := by
  unfold cutE
  have := (w 0).den_pos; have := (w 1).den_pos; have := (w 2).den_pos
  positivity

theorem cutCoef_cast (w : Fin 3 → ℚ) (j : Fin 3) : (cutCoef w j : ℚ) = cutE w * w j := by
  have hd : (w j).den ∣ cutE w := by
    unfold cutE
    match j with
    | 0 => exact Dvd.intro ((w 1).den * (w 2).den) (by ring)
    | 1 => exact Dvd.intro ((w 0).den * (w 2).den) (by ring)
    | 2 => exact Dvd.intro_left _ rfl
  obtain ⟨m, hm⟩ := hd
  simp only [cutCoef, hm, Nat.mul_div_cancel_left m (w j).den_pos]
  push_cast
  rw [← Rat.mul_den_eq_num (w j)]
  ring

theorem ZV.toV_smulE (v : ZV) (d : ℕ) (w : Fin 3 → ℚ) :
    (v.smul (cutE w)).toV (d * cutE w) = v.toV d := by
  have hE : (cutE w : ℚ) ≠ 0 := by exact_mod_cast (cutE_pos w).ne'
  funext j
  fin_cases j <;>
  · simp only [ZV.toV, ZV.smul, imul, Rat.mkRat_eq_div]
    push_cast
    field_simp

theorem ZV.toV_cut (v0 v1 v2 : ZV) (d : ℕ) (w : Fin 3 → ℚ) :
    (((v0.smul (cutCoef w 0)).add (v1.smul (cutCoef w 1))).add (v2.smul (cutCoef w 2))).toV
      (d * cutE w) =
      AtlasProjectiveLocalViewTree.cutPoint (tri3K (v0.toV d) (v1.toV d) (v2.toV d)) w := by
  have hE : (cutE w : ℚ) ≠ 0 := by exact_mod_cast (cutE_pos w).ne'
  funext j
  fin_cases j <;>
  · simp only [ZV.toV, ZV.smul, ZV.add, imul, iadd, Rat.mkRat_eq_div,
      AtlasProjectiveLocalViewTree.cutPoint, tri3K]
    push_cast
    rw [cutCoef_cast, cutCoef_cast, cutCoef_cast]
    field_simp

theorem cutZ_toRegion (r : Fin 8) (v0 v1 v2 : ZV) (d : ℕ) (w : Fin 3 → ℚ) (k : Fin 3) :
    (cutZ r v0 v1 v2 d w k).toRegion =
      .triangle r (AtlasProjectiveLocalViewTree.cutTriangle
        (tri3K (v0.toV d) (v1.toV d) (v2.toV d)) w k) := by
  fin_cases k <;> simp only [cutZ, ZR.toRegion] <;> congr 1 <;> funext i <;> fin_cases i <;>
    simp [AtlasProjectiveLocalViewTree.cutTriangle, tri3K, ZV.toV_cut, ZV.toV_smulE]

theorem chamberZ_toRegion : chamberZ.toRegion = .triangle 0 chamberTriangle := by
  simp only [chamberZ, ZR.toRegion]
  congr 1
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [tri3K, ZV.toV, chamberTriangle, Rat.mkRat_eq_div] <;> norm_num

theorem rootZ_ok : rootZ.ok = true := rfl

theorem rootZ_toInterval : rootZ.toInterval = AtlasPose.rootInterval ℚ := by
  apply interval_ext
  · rw [ZF.toInterval_min _ rootZ_ok]
    simp [ZF.pose, rootZ, AtlasPose.rootInterval, Rat.mkRat_eq_div]
  · rw [ZF.toInterval_max _ rootZ_ok]
    simp [ZF.pose, rootZ, AtlasPose.rootInterval, Rat.mkRat_eq_div]

theorem ZR.toRegion_tri (r : Fin 8) (v0 v1 v2 : ZV) (d : ℕ) :
    (ZR.tri r v0 v1 v2 d).toRegion = .triangle r (tri3K (v0.toV d) (v1.toV d) (v2.toV d)) := rfl

theorem ZF.with_reg_toInterval (f : ZF) (r : ZR) : ({ f with reg := r } : ZF).toInterval =
    f.toInterval := rfl

theorem ZF.with_reg_ok (f : ZF) (r : ZR) : ({ f with reg := r } : ZF).ok = f.ok := rfl

theorem ZF.half_reg (f : ZF) (i : Fin 5) (u : Bool) : (f.half i u).reg = f.reg := by
  fin_cases i <;> rfl

theorem Step.applyZ_spec (s : Step) (f : ZF) (h : f.ok = true) :
    (s.applyZ f).ok = true ∧
      ((s.applyZ f).toInterval, (s.applyZ f).reg.toRegion) =
        s.apply (f.toInterval, f.reg.toRegion) := by
  cases s with
  | half c u =>
      refine ⟨f.half_ok c u h, ?_⟩
      simp only [Step.applyZ, ZF.half_toInterval _ _ _ h, ZF.half_reg]
      cases u <;> rfl
  | root => exact ⟨h, by simp [Step.applyZ, Step.apply, ZF.with_reg_toInterval, chamberZ_toRegion]⟩
  | view k =>
      rcases hr : f.reg with _ | ⟨r, v0, v1, v2, d⟩
      · simp [Step.applyZ, Step.apply, hr, ZR.toRegion, h]
      · simp [Step.applyZ, Step.apply, hr, ZR.toRegion_tri, h, ZF.with_reg_toInterval,
          splitZ_toRegion, ZF.with_reg_ok]
  | cut w k =>
      rcases hr : f.reg with _ | ⟨r, v0, v1, v2, d⟩
      · simp [Step.applyZ, Step.apply, hr, ZR.toRegion, h]
      · simp [Step.applyZ, Step.apply, hr, ZR.toRegion_tri, h, ZF.with_reg_toInterval,
          cutZ_toRegion, ZF.with_reg_ok]

theorem foldl_applyZ : ∀ (steps : List Step) (f : ZF), f.ok = true →
    (steps.foldl (fun f s => s.applyZ f) f).ok = true ∧
      ((steps.foldl (fun f s => s.applyZ f) f).toInterval,
        (steps.foldl (fun f s => s.applyZ f) f).reg.toRegion) =
        steps.foldl (fun f s => s.apply f) (f.toInterval, f.reg.toRegion)
  | [], f, h => ⟨h, rfl⟩
  | s :: steps, f, h => by
      obtain ⟨h1, h2⟩ := s.applyZ_spec f h
      simp only [List.foldl_cons]
      rw [← h2]
      exact foldl_applyZ steps _ h1

theorem framePathZ_spec (steps : List Step) :
    (framePathZ steps).ok = true ∧
      ((framePathZ steps).toInterval, (framePathZ steps).reg.toRegion) = framePath steps := by
  have := foldl_applyZ steps rootZ rootZ_ok
  rw [rootZ_toInterval] at this
  exact this

theorem CTree.checkI_imp (hdr : Fin 64 → Option Header) (ch : ChartIndex) :
    ∀ (t : CTree) (f : ZF), f.ok = true → t.checkI hdr ch f = true →
      t.check hdr ch f.toInterval f.reg.toRegion = true
  | .cayleySplit c lo hi, f, hf, h => by
      simp only [CTree.checkI, Bool.and_eq_true] at h
      have k0 := lo.checkI_imp hdr ch _ (f.half_ok c false hf) h.1
      have k1 := hi.checkI_imp hdr ch _ (f.half_ok c true hf) h.2
      rw [ZF.half_toInterval _ _ _ hf, ZF.half_reg] at k0 k1
      simp only [CTree.check, Bool.and_eq_true]
      exact ⟨k0, k1⟩
  | .viewRoot child, f, hf, h => by
      simp only [CTree.checkI] at h
      have := child.checkI_imp hdr ch { f with reg := chamberZ } hf h
      rw [ZF.with_reg_toInterval, chamberZ_toRegion] at this
      simpa [CTree.check] using this
  | .viewSplit c0 c1 c2 c3, f, hf, h => by
      rcases hr : f.reg with _ | ⟨r, v0, v1, v2, d⟩
      · simp [CTree.checkI, hr] at h
      · simp only [CTree.checkI, hr, Bool.and_eq_true] at h
        obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
        have k0 := c0.checkI_imp hdr ch { f with reg := splitZ r v0 v1 v2 d 0 } hf h0
        have k1 := c1.checkI_imp hdr ch { f with reg := splitZ r v0 v1 v2 d 1 } hf h1
        have k2 := c2.checkI_imp hdr ch { f with reg := splitZ r v0 v1 v2 d 2 } hf h2
        have k3 := c3.checkI_imp hdr ch { f with reg := splitZ r v0 v1 v2 d 3 } hf h3
        simp only [ZF.with_reg_toInterval, splitZ_toRegion] at k0 k1 k2 k3
        simp only [ZR.toRegion, CTree.check, Bool.and_eq_true]
        exact ⟨⟨⟨k0, k1⟩, k2⟩, k3⟩
  | .viewCut w c0 c1 c2, f, hf, h => by
      rcases hr : f.reg with _ | ⟨r, v0, v1, v2, d⟩
      · simp [CTree.checkI, hr] at h
      · simp only [CTree.checkI, hr, Bool.and_eq_true, Bool.or_eq_true] at h
        obtain ⟨⟨⟨hw, h0⟩, h1⟩, h2⟩ := h
        simp only [ZR.toRegion, CTree.check, Bool.and_eq_true, Bool.or_eq_true]
        refine ⟨⟨⟨hw, ?_⟩, ?_⟩, ?_⟩
        · rcases h0 with h0 | h0
          · exact .inl h0
          · have := c0.checkI_imp hdr ch { f with reg := cutZ r v0 v1 v2 d w 0 } hf h0
            simp only [ZF.with_reg_toInterval, cutZ_toRegion] at this
            exact .inr this
        · rcases h1 with h1 | h1
          · exact .inl h1
          · have := c1.checkI_imp hdr ch { f with reg := cutZ r v0 v1 v2 d w 1 } hf h1
            simp only [ZF.with_reg_toInterval, cutZ_toRegion] at this
            exact .inr this
        · rcases h2 with h2 | h2
          · exact .inl h2
          · have := c2.checkI_imp hdr ch { f with reg := cutZ r v0 v1 v2 d w 2 } hf h2
            simp only [ZF.with_reg_toInterval, cutZ_toRegion] at this
            exact .inr this
  | .octahedron, f, _, h => by simpa [CTree.checkI, CTree.check] using h
  | .hole steps, f, _, h => by
      simp only [CTree.checkI, decide_eq_true_eq] at h
      have := (framePathZ_spec steps).2
      rw [h] at this
      simp [CTree.check, this]
  | .projective .., f, _, h | .global .., f, _, h | .mixed .., f, _, h
  | .projectiveLocal .., f, _, h | .tube .., f, _, h | .flip .., f, _, h | .corner, f, _, h => by
      rcases hr : f.reg with _ | ⟨r, v0, v1, v2, d⟩ <;>
        simp_all [CTree.checkI, CTree.check, ZR.toRegion]

/-- A chunk, checked over integer frames. -/
theorem chunkI_sound (hdr : Fin 64 → Option Header) (hhdr : HeadersCovered hdr)
    (hcorner : CornerCovered) (steps : List Step) (t : CTree)
    (h : t.checkI hdr 0 (framePathZ steps) = true)
    (hh : ∀ x ∈ t.holes, NoRupert 0 (framePath x).1 (framePath x).2) :
    NoRupert 0 (framePath steps).1 (framePath steps).2 := by
  have hs := framePathZ_spec steps
  have := t.checkI_imp hdr 0 _ hs.1 h
  rw [← hs.2]
  exact t.check_sound hdr hhdr hcorner 0 _ _ this hh

end Noperts.Triakis.ChartKernelTree
