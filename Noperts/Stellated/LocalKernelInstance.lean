module

public import Noperts.Stellated.LocalKernelSound
public import Noperts.Stellated.LocalKernelFast
public import Noperts.Stellated.AtlasProjectiveLocalViewTree

@[expose] public section

/-!
# Kernel-path decision instances for local view tables

Imported only by kernel-checked (`decide +kernel`) files: `Box.ViewValid` is
decided by the integer checker `LocalKernel.viewValidN` (sound by
`viewValidN_sound`), falling back to the rational specification otherwise, and
the row/range instances are re-derived so they pick it up.  The native path
keeps the instances of `AtlasProjectiveLocalCertificate`.
-/

namespace Noperts.Stellated.LocalKernel

open AtlasProjectiveLocalCertificate AtlasProjectiveLocalViewTree

/-- Equality of view triangles entry by entry (the generic decision procedure for
functions on `Fin 3 × Fin 3` enumerates `Finset.univ` in the kernel). -/
instance (priority := high) instTriangleDecEqKernel (s t : Fin 3 → Fin 3 → ℚ) : Decidable (s = t) :=
  decidable_of_iff (s 0 0 = t 0 0 ∧ s 0 1 = t 0 1 ∧ s 0 2 = t 0 2 ∧ s 1 0 = t 1 0 ∧
      s 1 1 = t 1 1 ∧ s 1 2 = t 1 2 ∧ s 2 0 = t 2 0 ∧ s 2 1 = t 2 1 ∧ s 2 2 = t 2 2) (by
    constructor
    · rintro ⟨h00, h01, h02, h10, h11, h12, h20, h21, h22⟩
      funext i j
      fin_cases i <;> fin_cases j <;> assumption
    · rintro rfl
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)


/-- Entry-wise equality of view triangles. -/
def triEq9 (s t : AtlasProjectiveView.Triangle ℚ) : Bool :=
  decide (s 0 0 = t 0 0) && decide (s 0 1 = t 0 1) && decide (s 0 2 = t 0 2) &&
  decide (s 1 0 = t 1 0) && decide (s 1 1 = t 1 1) && decide (s 1 2 = t 1 2) &&
  decide (s 2 0 = t 2 0) && decide (s 2 1 = t 2 1) && decide (s 2 2 = t 2 2)

theorem triEq9_iff (s t : AtlasProjectiveView.Triangle ℚ) : triEq9 s t = true ↔ s = t := by
  simp only [triEq9, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨h00, h01⟩, h02⟩, h10⟩, h11⟩, h12⟩, h20⟩, h21⟩, h22⟩
    funext i j
    fin_cases i <;> fin_cases j <;> assumption
  · rintro rfl
    exact ⟨⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩

/-- The triangle with rows `a, b, c`. -/
def tri3 (a b c : AtlasProjectiveView.Vector ℚ) : AtlasProjectiveView.Triangle ℚ :=
  fun i => match i with | 0 => a | 1 => b | 2 => c

/-- The conditions of a split row, with the children's triangles from shared midpoints. -/
def splitRowOk (get : ℕ → Row) (size id : ℕ) (children : Fin 4 → ℕ) (root : Fin 8)
    (t : AtlasProjectiveView.Triangle ℚ) : Bool :=
  let m01 := Noperts.ProjectiveView.midpoint (t 0) (t 1)
  let m02 := Noperts.ProjectiveView.midpoint (t 0) (t 2)
  let m12 := Noperts.ProjectiveView.midpoint (t 1) (t 2)
  let m20 := Noperts.ProjectiveView.midpoint (t 2) (t 0)
  let one := fun (c : ℕ) (e : AtlasProjectiveView.Triangle ℚ) =>
    Nat.blt id c && Nat.blt c size && decide ((get c).root = root) && triEq9 (get c).triangle e
  one (children 0) (tri3 (t 0) m01 m02) && one (children 1) (tri3 m01 (t 1) m12) &&
    one (children 2) (tri3 m02 m12 (t 2)) && one (children 3) (tri3 m01 m12 m20)

theorem split_tri3 (t : AtlasProjectiveView.Triangle ℚ) (k : Fin 4) :
    Noperts.ProjectiveView.split t k = (match k with
      | 0 => tri3 (t 0) (Noperts.ProjectiveView.midpoint (t 0) (t 1))
          (Noperts.ProjectiveView.midpoint (t 0) (t 2))
      | 1 => tri3 (Noperts.ProjectiveView.midpoint (t 0) (t 1)) (t 1)
          (Noperts.ProjectiveView.midpoint (t 1) (t 2))
      | 2 => tri3 (Noperts.ProjectiveView.midpoint (t 0) (t 2))
          (Noperts.ProjectiveView.midpoint (t 1) (t 2)) (t 2)
      | 3 => tri3 (Noperts.ProjectiveView.midpoint (t 0) (t 1))
          (Noperts.ProjectiveView.midpoint (t 1) (t 2)) (Noperts.ProjectiveView.midpoint (t 2) (t 0))) := by
  funext i
  fin_cases k <;> fin_cases i <;> rfl

theorem splitRowOk_iff (symmetryIndex : OrbitIndex) (r : ℚ) (get : ℕ → Row) (size id : ℕ)
    (children : Fin 4 → ℕ) (root : Fin 8) (t : AtlasProjectiveView.Triangle ℚ) :
    splitRowOk get size id children root t = true ↔
      (Row.split id children root t).ValidAt symmetryIndex r get size := by
  simp only [splitRowOk, Row.ValidAt, Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq, triEq9_iff]
  constructor
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ k
    fin_cases k
    · exact ⟨h0.1.1.1, h0.1.1.2, h0.1.2, h0.2.trans (split_tri3 t 0).symm⟩
    · exact ⟨h1.1.1.1, h1.1.1.2, h1.1.2, h1.2.trans (split_tri3 t 1).symm⟩
    · exact ⟨h2.1.1.1, h2.1.1.2, h2.1.2, h2.2.trans (split_tri3 t 2).symm⟩
    · exact ⟨h3.1.1.1, h3.1.1.2, h3.1.2, h3.2.trans (split_tri3 t 3).symm⟩
  · intro h
    have e := fun k => (h k).2.2.2.trans (split_tri3 t k)
    exact ⟨⟨⟨⟨⟨⟨(h 0).1, (h 0).2.1⟩, (h 0).2.2.1⟩, e 0⟩, ⟨⟨⟨(h 1).1, (h 1).2.1⟩, (h 1).2.2.1⟩, e 1⟩⟩,
      ⟨⟨⟨(h 2).1, (h 2).2.1⟩, (h 2).2.2.1⟩, e 2⟩⟩, ⟨⟨⟨(h 3).1, (h 3).2.1⟩, (h 3).2.2.1⟩, e 3⟩⟩

/-! ### Split rows by cross-multiplication

The children's triangles are stored, so a split row only has to *check* that each vertex is
a parent vertex or the midpoint of two: `2 c = a + b` on numerators and denominators, with no
rational normalization. -/

/-- The sign–magnitude test of `w = (u + v) r`, from `|u|, |v|, |w|`, `r` and the signs. -/
def smTest (A B C r : ℕ) (sa sb sc : Bool) : Bool :=
  cond (sa == sb) (Nat.beq C (Nat.mul (Nat.add A B) r) && (Nat.beq C 0 || sc == sa))
    (cond (Nat.ble B A) (Nat.beq C (Nat.mul (Nat.sub A B) r) && (Nat.beq C 0 || sc == sa))
      (Nat.beq C (Nat.mul (Nat.sub B A) r) && (Nat.beq C 0 || sc == sb)))

theorem smTest_imp (A B C r : ℕ) (sa sb sc : Bool) (h : smTest A B C r sa sb sc = true) :
    (sa = sb ∧ C = (A + B) * r ∧ (C = 0 ∨ sc = sa)) ∨
      (sa ≠ sb ∧ B ≤ A ∧ C = (A - B) * r ∧ (C = 0 ∨ sc = sa)) ∨
      (sa ≠ sb ∧ A < B ∧ C = (B - A) * r ∧ (C = 0 ∨ sc = sb)) := by
  unfold smTest at h
  by_cases hs : sa = sb
  · have e : (sa == sb) = true := by simp [hs]
    rw [e, Bool.cond_true] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, beq_iff_eq, Nat.mul_eq,
      Nat.add_eq] at h
    exact Or.inl ⟨hs, h.1, h.2⟩
  · have e : (sa == sb) = false := by simpa using hs
    rw [e, Bool.cond_false] at h
    by_cases hab : B ≤ A
    · have e2 : Nat.ble B A = true := Nat.ble_eq.mpr hab
      rw [e2, Bool.cond_true] at h
      simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, beq_iff_eq, Nat.mul_eq,
        Nat.sub_eq] at h
      exact Or.inr (Or.inl ⟨hs, hab, h.1, h.2⟩)
    · have e2 : Nat.ble B A = false := by
        rw [← Bool.not_eq_true, Nat.ble_eq]; exact hab
      rw [e2, Bool.cond_false] at h
      simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, beq_iff_eq, Nat.mul_eq,
        Nat.sub_eq] at h
      exact Or.inr (Or.inr ⟨hs, by omega, h.1, h.2⟩)

theorem smTest_sound (u v w : ℤ) (r : ℕ)
    (h : smTest u.natAbs v.natAbs w.natAbs r (decide (u < 0)) (decide (v < 0)) (decide (w < 0)) =
      true) : w = (u + v) * r := by
  have key : w.natAbs = (u + v).natAbs * r ∧ (w.natAbs = 0 ∨ (w < 0 ↔ u + v < 0)) := by
    rcases smTest_imp _ _ _ _ _ _ _ h with ⟨hs, hC, hz⟩ | ⟨hs, hab, hC, hz⟩ | ⟨hs, hab, hC, hz⟩
    · rw [decide_eq_decide] at hs
      have e : (u + v).natAbs = u.natAbs + v.natAbs := by
        by_cases hu : u < 0 <;> omega
      rw [e]
      refine ⟨hC, ?_⟩
      rcases hz with hz | hz
      · exact Or.inl hz
      · rw [decide_eq_decide] at hz
        by_cases h0 : w.natAbs = 0
        · exact Or.inl h0
        · right; by_cases hu : u < 0 <;> omega
    · have hs' : ¬ (u < 0 ↔ v < 0) := fun h' => hs (decide_eq_decide.mpr h')
      have e : (u + v).natAbs = u.natAbs - v.natAbs := by
        by_cases hu : u < 0 <;> omega
      rw [e]
      refine ⟨hC, ?_⟩
      rcases hz with hz | hz
      · exact Or.inl hz
      · rw [decide_eq_decide] at hz
        by_cases h0 : w.natAbs = 0
        · exact Or.inl h0
        · right
          have : u.natAbs - v.natAbs ≠ 0 := by
            intro h3; rw [h3, Nat.zero_mul] at hC; exact h0 hC
          by_cases hu : u < 0 <;> omega
    · have hs' : ¬ (u < 0 ↔ v < 0) := fun h' => hs (decide_eq_decide.mpr h')
      have e : (u + v).natAbs = v.natAbs - u.natAbs := by
        by_cases hu : u < 0 <;> omega
      rw [e]
      refine ⟨hC, ?_⟩
      rcases hz with hz | hz
      · exact Or.inl hz
      · rw [decide_eq_decide] at hz
        by_cases h0 : w.natAbs = 0
        · exact Or.inl h0
        · right; by_cases hu : u < 0 <;> omega
  obtain ⟨h1, h2⟩ := key
  have hc : ((w.natAbs : ℕ) : ℤ) = ((u + v).natAbs : ℤ) * r := by exact_mod_cast h1
  rcases h2 with h2 | h2
  · have hw : w = 0 := by omega
    have : ((u + v).natAbs : ℤ) * r = 0 := by rw [← hc, h2]; rfl
    rcases mul_eq_zero.mp this with h3 | h3
    · have : u + v = 0 := by omega
      rw [hw, this, zero_mul]
    · rw [hw, h3, mul_zero]
  · by_cases hw : w < 0
    · have hs : u + v < 0 := h2.mp hw
      rw [Int.ofNat_natAbs_of_nonpos hw.le, Int.ofNat_natAbs_of_nonpos hs.le] at hc
      linarith
    · have hs : ¬ u + v < 0 := fun h => hw (h2.mpr h)
      rw [Int.natAbs_of_nonneg (by omega), Int.natAbs_of_nonneg (by omega)] at hc
      linarith

/-- `c = (a + b) / 2`, cross-multiplied in sign–magnitude form (all products are `Nat`
products, which the kernel evaluates with GMP). -/
def midQ (c a b : ℚ) : Bool :=
  smTest (Nat.mul a.num.natAbs b.den) (Nat.mul b.num.natAbs a.den)
    (Nat.mul (Nat.mul (Nat.mul 2 c.num.natAbs) a.den) b.den) c.den
    (decide (a.num < 0)) (decide (b.num < 0)) (decide (c.num < 0))

theorem midQ_sound (c a b : ℚ) (h : midQ c a b = true) : c = (a + b) / 2 := by
  have pa : (0 : ℤ) < a.den := by exact_mod_cast a.den_pos
  have pb : (0 : ℤ) < b.den := by exact_mod_cast b.den_pos
  have e1 : Nat.mul a.num.natAbs b.den = (a.num * b.den).natAbs := by
    rw [Int.natAbs_mul]; rfl
  have e2 : Nat.mul b.num.natAbs a.den = (b.num * a.den).natAbs := by
    rw [Int.natAbs_mul]; rfl
  have e3 : Nat.mul (Nat.mul (Nat.mul 2 c.num.natAbs) a.den) b.den =
      (2 * c.num * a.den * b.den).natAbs := by
    simp only [Int.natAbs_mul]; rfl
  have s1 : decide (a.num < 0) = decide (a.num * b.den < 0) := by
    simp only [decide_eq_decide]
    constructor
    · intro h; nlinarith
    · intro h; by_contra h'; push Not at h'; nlinarith
  have s2 : decide (b.num < 0) = decide (b.num * a.den < 0) := by
    simp only [decide_eq_decide]
    constructor
    · intro h; nlinarith
    · intro h; by_contra h'; push Not at h'; nlinarith
  have s3 : decide (c.num < 0) = decide (2 * c.num * a.den * b.den < 0) := by
    simp only [decide_eq_decide]
    have hab : (0 : ℤ) < 2 * a.den * b.den := by positivity
    constructor
    · intro h; nlinarith
    · intro h; by_contra h'; push Not at h'; nlinarith
  rw [midQ, e1, e2, e3, s1, s2, s3] at h
  have h' := smTest_sound _ _ _ _ h
  have ha := Rat.num_div_den a
  have hb := Rat.num_div_den b
  have hc := Rat.num_div_den c
  have da : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_nz
  have db : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_nz
  have dc : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_nz
  have h'' : (2 * c.num * a.den * b.den : ℚ) = (a.num * b.den + b.num * a.den) * c.den := by
    exact_mod_cast h'
  rw [← ha, ← hb, ← hc]
  field_simp
  linear_combination h''

/-- Vertex `c` is the midpoint of `a` and `b`. -/
def midV (c a b : AtlasProjectiveView.Vector ℚ) : Bool :=
  midQ (c 0) (a 0) (b 0) && midQ (c 1) (a 1) (b 1) && midQ (c 2) (a 2) (b 2)

def eqV (c a : AtlasProjectiveView.Vector ℚ) : Bool :=
  decide (c 0 = a 0) && decide (c 1 = a 1) && decide (c 2 = a 2)

theorem midV_sound {c a b : AtlasProjectiveView.Vector ℚ} (h : midV c a b = true) :
    c = Noperts.ProjectiveView.midpoint a b := by
  simp only [midV, Bool.and_eq_true] at h
  funext i
  fin_cases i
  · exact midQ_sound _ _ _ h.1.1
  · exact midQ_sound _ _ _ h.1.2
  · exact midQ_sound _ _ _ h.2

theorem eqV_sound {c a : AtlasProjectiveView.Vector ℚ} (h : eqV c a = true) : c = a := by
  simp only [eqV, Bool.and_eq_true, decide_eq_true_eq] at h
  funext i
  fin_cases i
  · exact h.1.1
  · exact h.1.2
  · exact h.2

theorem tri3_eta (T : AtlasProjectiveView.Triangle ℚ) : T = tri3 (T 0) (T 1) (T 2) := by
  funext i
  fin_cases i <;> rfl

/-- One child of a split row: its header and its three vertices. -/
def childF (get : ℕ → Row) (size id c : ℕ) (root : Fin 8)
    (va vb vc : AtlasProjectiveView.Vector ℚ → Bool) : Bool :=
  Nat.blt id c && Nat.blt c size && decide ((get c).root = root) &&
    va ((get c).triangle 0) && vb ((get c).triangle 1) && vc ((get c).triangle 2)

theorem childF_sound (get : ℕ → Row) (size id c : ℕ) (root : Fin 8)
    {va vb vc : AtlasProjectiveView.Vector ℚ → Bool} {A B C : AtlasProjectiveView.Vector ℚ}
    (hA : ∀ v, va v = true → v = A) (hB : ∀ v, vb v = true → v = B)
    (hC : ∀ v, vc v = true → v = C) (h : childF get size id c root va vb vc = true) :
    (Nat.blt id c && Nat.blt c size && decide ((get c).root = root) &&
      triEq9 (get c).triangle (tri3 A B C)) = true := by
  simp only [childF, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  simp only [Bool.and_eq_true, h1, h2, h3, and_self, true_and]
  rw [triEq9_iff, tri3_eta (get c).triangle, hA _ h4, hB _ h5, hC _ h6]

theorem midpoint_comm (a b : AtlasProjectiveView.Vector ℚ) :
    Noperts.ProjectiveView.midpoint a b = Noperts.ProjectiveView.midpoint b a := by
  funext i; simp only [Noperts.ProjectiveView.midpoint]; ring

/-- A split row, with the children's vertices checked against the parent's: the three
midpoints once (as stored in children `0` and `1`), the other copies by equality. -/
def splitRowOkF (get : ℕ → Row) (size id : ℕ) (children : Fin 4 → ℕ) (root : Fin 8)
    (t : AtlasProjectiveView.Triangle ℚ) : Bool :=
  let T := fun (k : Fin 4) => (get (children k)).triangle
  let m01 := T 0 1
  let m02 := T 0 2
  let m12 := T 1 2
  midV m01 (t 0) (t 1) && midV m02 (t 0) (t 2) && midV m12 (t 1) (t 2) &&
  childF get size id (children 0) root (eqV · (t 0)) (eqV · m01) (eqV · m02) &&
  childF get size id (children 1) root (eqV · m01) (eqV · (t 1)) (eqV · m12) &&
  childF get size id (children 2) root (eqV · m02) (eqV · m12) (eqV · (t 2)) &&
  childF get size id (children 3) root (eqV · m01) (eqV · m12) (eqV · m02)

theorem splitRowOkF_sound (symmetryIndex : OrbitIndex) (r : ℚ) (get : ℕ → Row) (size id : ℕ)
    (children : Fin 4 → ℕ) (root : Fin 8) (t : AtlasProjectiveView.Triangle ℚ)
    (h : splitRowOkF get size id children root t = true) :
    (Row.split id children root t).ValidAt symmetryIndex r get size := by
  rw [← splitRowOk_iff]
  simp only [splitRowOkF, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hm01, hm02⟩, hm12⟩, h0⟩, h1⟩, h2⟩, h3⟩ := h
  rw [midV_sound hm01, midV_sound hm02] at h0
  rw [midV_sound hm01, midV_sound hm12] at h1
  rw [midV_sound hm02, midV_sound hm12] at h2
  rw [midV_sound hm01, midV_sound hm02, midV_sound hm12] at h3
  simp only [splitRowOk, Bool.and_eq_true]
  have E : ∀ a : AtlasProjectiveView.Vector ℚ, ∀ v, eqV v a = true → v = a :=
    fun _ _ hv => eqV_sound hv
  rw [midpoint_comm (t 2) (t 0)]
  exact ⟨⟨⟨by simpa using childF_sound get size id _ root (E _) (E _) (E _) h0,
    by simpa using childF_sound get size id _ root (E _) (E _) (E _) h1⟩,
    by simpa using childF_sound get size id _ root (E _) (E _) (E _) h2⟩,
    by simpa using childF_sound get size id _ root (E _) (E _) (E _) h3⟩

instance (priority := high) instViewValidKernel (box : Box) : Decidable box.ViewValid :=
  if h : viewValidZ box = true then isTrue (viewValidZ_sound box h)
  else decidable_of_iff _ box.viewValid_iff_fastB.symm

instance (priority := high) instRowValidAtKernel (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size : ℕ) (row : Row) :
    Decidable (row.ValidAt symmetryIndex r get size) := by
  cases row with
  | split id children root t =>
      exact if hf : splitRowOkF get size id children root t = true then
        isTrue (splitRowOkF_sound symmetryIndex r get size id children root t hf)
      else decidable_of_iff _ (splitRowOk_iff symmetryIndex r get size id children root t)
  | certificate id box => simp only [Row.ValidAt]; infer_instance
  | cut id children root t w => simp only [Row.ValidAt]; infer_instance

instance (priority := high) instRowsValidRangeAtKernel (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size start count : ℕ) :
    Decidable (RowsValidRangeAt symmetryIndex r get size start count) := by
  unfold RowsValidRangeAt; infer_instance

/-- An 8-ary tree of depth `d` with leaves in `α` (`Fin 8 → … → α`). -/
def Tree8 (α : Type) : ℕ → Type
  | 0 => α
  | d + 1 => Fin 8 → Tree8 α d

/-- Leaf `i` of a depth-`d` tree: digit `d-1` of `i` (base 8) selects the top
branch, …, digit `0` the leaf.  `O(d)` `Fin.cons` walks of at most 8 cells. -/
def Tree8.get {α : Type} : (d : ℕ) → Tree8 α d → ℕ → α
  | 0, t, _ => t
  | d + 1, t, i => Tree8.get d (t ⟨i / 8 ^ d % 8, Nat.mod_lt _ (by decide)⟩) i

end Noperts.Stellated.LocalKernel
