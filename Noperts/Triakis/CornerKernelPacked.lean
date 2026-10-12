module

public import Noperts.Triakis.CornerKernelLeaf
public import Noperts.Triakis.PackedDigits

@[expose] public section

/-!
# A packed cheap bound for fact polynomials

`cheapP` walks the terms of a fact polynomial one by one.  `cheapS` evaluates all terms at
once: term `t` owns a block of eight `W`-bit digits (its value at `|x|` and its seven
partial derivatives) of one natural number, and one more `W`-bit digit of a second number
(its value at `|x| + H`).  For each variable and each exponent `e` occurring in it, the
blocks of the terms with that exponent are selected with a precomputed mask and multiplied
by `x^e` (the derivative digit gets `e x^(e-1)` times the value digit); the signs come
from masks too, and `% (2^(8W) - 1)` sums the blocks.  So a leaf costs a few hundred
GMP-backed kernel operations instead of a walk over every term.  The masks (`PFP`) are
computed once per fact (`mkPFP`).

`cheapS_imp` shows that, when every digit stays below `2^W` (checked by a cheap bound on
the inputs), `cheapS` computes exactly the sums of the integer cheap bound (`cheapI`).
-/

namespace Noperts.Triakis.CornerKernel

open SparsePoly PackedDigits

/-! ## The packed form of a fact polynomial -/

abbrev Term := Mono × ℕ × Bool

/-- A group of terms (those whose exponent of a variable is `e`), as masks over the term
blocks (`mask`) and over the majorant digits (`maskT`). -/
structure VG where
  e : ℕ
  mask : ℕ
  maskT : ℕ
deriving DecidableEq, Inhabited

structure PFP where
  W : ℕ
  N : ℕ
  csum : ℕ
  sok : Bool
  C : ℕ
  CT : ℕ
  vars : List (List VG)
  dg : List VG
  CS : ℕ
  odd : List ℕ
  vmask : ℕ
  wmask : ℕ
  bmod : ℕ
  /-- The monomial factor `m` of the fact polynomial. -/
  mono : Mono
deriving DecidableEq, Inhabited

/-- All-ones digits on the terms satisfying `p`. -/
def selMask (B : ℕ) (S : List Term) (p : Term → Bool) : ℕ :=
  digB B (S.map fun t => if p t then 2 ^ B - 1 else 0)

def expAt (m : Mono) (i : ℕ) : ℕ := m.getD i 0

/-- The groups of the nonzero values of `x` over the terms. -/
def groupsOf (W : ℕ) (S : List Term) (x : Term → ℕ) : List VG :=
  ((S.map x).filter (· ≠ 0)).dedup.map fun e =>
    ⟨e, selMask (8 * W) S (fun t => x t == e), selMask W S (fun t => x t == e)⟩

def mkPFP (W : ℕ) (fp : FactPoly) : PFP :=
  { W := W
    N := maxDegN fp.S
    csum := (fp.S.map fun t => t.2.1).sum
    sok := fp.S.all fun t => decide (t.1.length ≤ 7)
    C := digB (8 * W) (fp.S.map fun t => t.2.1)
    CT := digB W (fp.S.map fun t => t.2.1)
    vars := (List.range 7).map fun i => groupsOf W fp.S (fun t => expAt t.1 i)
    dg := groupsOf W fp.S (fun t => maxDegN fp.S - degM t.1)
    CS := selMask (8 * W) fp.S (fun t => t.2.2)
    odd := (List.range 7).map fun i => selMask (8 * W) fp.S (fun t => expAt t.1 i % 2 == 1)
    vmask := digB (8 * W) (fp.S.map fun _ => 2 ^ W - 1)
    wmask := 2 ^ W - 1
    bmod := 2 ^ (8 * W) - 1
    mono := fp.m }

/-- The digit width used for the generated tables. -/
def packedW : ℕ := 256

/-! ## The checker -/

structure PP where
  P : ℕ
  T : ℕ

/-- One group step: multiply the selected blocks by `a^e` and add `e a^(e-1)` times their
value digit at shift `sh`; multiply the selected majorant digits by `u^e`. -/
def grpStep (vmask sh a u : ℕ) (g : VG) (P T : ℕ) : PP :=
  let sel := Nat.land P g.mask
  let selT := Nat.land T g.maskT
  ⟨Nat.add (Nat.add (Nat.sub P sel) (Nat.mul sel (Nat.pow a g.e)))
      (Nat.mul (Nat.shiftLeft (Nat.land sel vmask) sh) (Nat.mul g.e (Nat.pow a (Nat.sub g.e 1)))),
    Nat.add (Nat.sub T selT) (Nat.mul selT (Nat.pow u g.e))⟩

/-- The groups of one variable with value `a`, majorant point `u`, derivative shift `sh`. -/
def grpR (vmask sh a u : ℕ) (gs : List VG) : ℕ → ℕ → PP :=
  @List.rec VG (fun _ => ℕ → ℕ → PP) (fun P T => ⟨P, T⟩)
    (fun g _ ih P T =>
      let r := grpStep vmask sh a u g P T
      ih r.P r.T) gs

/-- The homogenizing powers of `D`. -/
def grpD (D : ℕ) (gs : List VG) : ℕ → ℕ → PP :=
  @List.rec VG (fun _ => ℕ → ℕ → PP) (fun P T => ⟨P, T⟩)
    (fun g _ ih P T =>
      let sel := Nat.land P g.mask
      let selT := Nat.land T g.maskT
      let d := Nat.pow D g.e
      ih (Nat.add (Nat.sub P sel) (Nat.mul sel d)) (Nat.add (Nat.sub T selT) (Nat.mul selT d))) gs

/-- All variables, with center `xs` and radii `hs`. -/
def varsR (W vmask : ℕ) (vs : List (List VG)) : List ℤ → List ℤ → ℕ → ℕ → ℕ → PP :=
  @List.rec (List VG) (fun _ => List ℤ → List ℤ → ℕ → ℕ → ℕ → PP) (fun _ _ _ P T => ⟨P, T⟩)
    (fun gs _ ih xs hs sh P T =>
      let a := Int.natAbs (xs.headD 0)
      let r := grpR vmask sh a (Nat.add a (Int.toNat (hs.headD 0))) gs P T
      ih xs.tail hs.tail (Nat.add sh W) r.P r.T) vs

def isNegI : ℤ → Bool
  | .ofNat _ => false
  | .negSucc _ => true

/-- The mask of the negative terms: `acc` xor the odd-exponent masks of negative coordinates. -/
def negR (odd : List ℕ) : List ℤ → ℕ → ℕ :=
  @List.rec ℕ (fun _ => List ℤ → ℕ → ℕ) (fun _ acc => acc)
    (fun o _ ih xs acc => ih xs.tail (cond (isNegI (xs.headD 0)) (Nat.xor acc o) acc)) odd

structure LL where
  lin : ℕ
  L : ℕ

/-- The linear part (`lin`) and its majorant (`L`) from the summed positive and negative
blocks `sp`, `sn` and the radii `hs`. -/
def linR (W wmask sp sn : ℕ) : List ℤ → ℕ → ℕ → ℕ → LL :=
  @List.rec ℤ (fun _ => ℕ → ℕ → ℕ → LL) (fun _ lin L => ⟨lin, L⟩)
    (fun h _ ih sh lin L =>
      let p := Nat.land (Nat.shiftRight sp sh) wmask
      let q := Nat.land (Nat.shiftRight sn sh) wmask
      let hn := Int.toNat h
      ih (Nat.add sh W) (Nat.add lin (Nat.mul hn (cond (Nat.ble p q) (Nat.sub q p) (Nat.sub p q))))
        (Nat.add L (Nat.mul hn (Nat.add p q))))

/-- `max D (|xᵢ| + hᵢ)`. -/
def maxR (D : ℕ) : List ℤ → List ℤ → ℕ :=
  @List.rec ℤ (fun _ => List ℤ → ℕ) (fun _ => D)
    (fun x _ ih hs => Nat.max (Nat.add (Int.natAbs x) (Int.toNat (hs.headD 0))) (ih hs.tail))

/-- The packed cheap bound of `pf` on the box with center `X / D` and radii `H / D`. -/
def cheapS (pf : PFP) (D : ℕ) (X H : List ℤ) : Bool :=
  let W := pf.W
  let r1 := varsR W pf.vmask pf.vars X H W pf.C pf.CT
  let r := grpD D pf.dg r1.P r1.T
  let neg := negR pf.odd X pf.CS
  let Pn := Nat.land r.P neg
  let sp := Nat.mod (Nat.sub r.P Pn) pf.bmod
  let sn := Nat.mod Pn pf.bmod
  let T := Nat.mod r.T pf.wmask
  let vP := Nat.land sp pf.wmask
  let vN := Nat.land sn pf.wmask
  let ll := linR W pf.wmask sp sn H W 0 0
  pf.sok && Nat.blt 0 D &&
    Nat.blt (Nat.mul (Nat.mul pf.csum (Nat.succ pf.N)) (Nat.pow (maxR D X H) pf.N)) pf.wmask &&
    Nat.ble (Nat.add (Nat.add vN ll.lin) T) (Nat.add (Nat.add vP (Nat.add vP vN)) ll.L)

/-- The variables of `m` are nonnegative on the box: `Hᵢ ≤ Xᵢ` wherever `mᵢ ≠ 0`. -/
def monoOkR (m : Mono) : List ℤ → List ℤ → Bool :=
  @List.rec ℕ (fun _ => List ℤ → List ℤ → Bool) (fun _ _ => true)
    (fun e _ ih xs hs => (Nat.beq e 0 || decide (hs.headD 0 ≤ xs.headD 0)) && ih xs.tail hs.tail) m

theorem monoOkR_sound : ∀ (m : Mono) (X H : List ℤ), monoOkR m X H = true →
    ∀ i < m.length, m.getD i 0 = 0 ∨ H.getD i 0 ≤ X.getD i 0
  | [], _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | e :: m, X, H, h, i, hi => by
      have h' : (Nat.beq e 0 || decide (H.headD 0 ≤ X.headD 0)) = true ∧
          monoOkR m X.tail H.tail = true := by
        simpa [monoOkR] using h
      cases i with
      | zero =>
          rcases Bool.or_eq_true_iff.mp h'.1 with h0 | h0
          · exact Or.inl (by simpa using Nat.eq_of_beq_eq_true h0)
          · right
            have := of_decide_eq_true h0
            cases X <;> cases H <;> simp_all
      | succ i =>
          have := monoOkR_sound m X.tail H.tail h'.2 i (by simpa using hi)
          cases X <;> cases H <;> simp_all

/-! ## Soundness: blocks -/

section blocks
variable (W : ℕ)

/-- A term's block: eight `W`-bit digits. -/
def blkF (c : ℕ → ℕ) : ℕ := digB W ((List.range 8).map c)

theorem blkF_lt (c : ℕ → ℕ) (hc : ∀ j < 8, c j < 2 ^ W) : blkF W c < 2 ^ (8 * W) := by
  have := digB_lt W (List.range 8) c (fun j hj => hc j (List.mem_range.mp hj))
  simpa [blkF, Nat.mul_comm] using this

theorem blkF_add (c d : ℕ → ℕ) : blkF W c + blkF W d = blkF W fun j => c j + d j :=
  digB_map_add W _ c d

theorem digB_map_mul' (B c : ℕ) {α : Type*} (L : List α) (f : α → ℕ) :
    digB B (L.map f) * c = digB B (L.map fun t => f t * c) := by
  rw [Nat.mul_comm, digB_map_mul]
  exact digB_map_congr B fun t _ => Nat.mul_comm _ _

theorem blkF_mul (x : ℕ) (c : ℕ → ℕ) : x * blkF W c = blkF W fun j => x * c j :=
  digB_map_mul W x _ c

theorem blkF_zero : blkF W (fun _ => 0) = 0 := digB_map_zero W _

theorem digB_single (B x : ℕ) : ∀ (n s : ℕ), s < n →
    digB B ((List.range n).map fun j => if j = s then x else 0) = x * 2 ^ (B * s)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, s, h => by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, digB_cons]
      cases s with
      | zero =>
          have : ((fun j => if j = 0 then x else 0) ∘ Nat.succ) = fun _ => 0 := by
            funext j; simp
          rw [this, digB_map_zero]
          simp
      | succ s =>
          have : ((fun j => if j = s + 1 then x else 0) ∘ Nat.succ) =
              fun j => if j = s then x else 0 := by
            funext j; simp
          rw [this, digB_single B x n s (by omega),
            show (if (0 : ℕ) = s + 1 then x else 0) = 0 by simp, zero_add,
            show B * (s + 1) = B + B * s by ring, pow_add]
          ring

theorem blkF_single (x s : ℕ) (hs : s < 8) :
    blkF W (fun j => if j = s then x else 0) = x * 2 ^ (W * s) :=
  digB_single W x 8 s hs

theorem blkF_mod (c : ℕ → ℕ) (h0 : c 0 < 2 ^ W) : blkF W c % 2 ^ W = c 0 := by
  simp only [blkF, List.range_succ_eq_map, List.map_cons, digB_cons]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]

theorem blkF_digit (c : ℕ → ℕ) (hc : ∀ j < 8, c j < 2 ^ W) (j : ℕ) (hj : j < 8) :
    (blkF W c >>> (W * j)) &&& (2 ^ W - 1) = c j := by
  rw [blkF, digB_digit W _ (fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hc i (List.mem_range.mp hi))]
  simp [List.getD_eq_getElem?_getD, hj]

theorem blkF_sum {α : Type*} (L : List α) (c : α → ℕ → ℕ) :
    (L.map fun t => blkF W (c t)).sum = blkF W fun j => (L.map fun t => c t j).sum := by
  induction L with
  | nil => simp [blkF_zero]
  | cons t L ih => simp only [List.map_cons, List.sum_cons, ih, blkF_add]

end blocks

/-! ## Soundness: one group step -/

section step
variable {W : ℕ}

/-- The effect of a group step on a term's digits. -/
def stepCell (a e k : ℕ) (c : ℕ → ℕ) : ℕ → ℕ :=
  fun j => a ^ e * c j + if j = k + 1 then e * a ^ (e - 1) * c 0 else 0

theorem stepCell_zero (a k : ℕ) (c : ℕ → ℕ) : stepCell a 0 k c = c := by
  funext j; simp [stepCell]

theorem grpStep_spec (S : List Term) (p : Term → Bool) (e a u k : ℕ) (hk : k + 1 < 8)
    (cs : Term → ℕ → ℕ) (ts : Term → ℕ)
    (hcs : ∀ t ∈ S, ∀ j < 8, cs t j < 2 ^ W) (hts : ∀ t ∈ S, ts t < 2 ^ W) :
    grpStep (digB (8 * W) (S.map fun _ => 2 ^ W - 1)) (W * (k + 1)) a u
        ⟨e, selMask (8 * W) S p, selMask W S p⟩
        (digB (8 * W) (S.map fun t => blkF W (cs t))) (digB W (S.map ts)) =
      ⟨digB (8 * W) (S.map fun t => blkF W (if p t then stepCell a e k (cs t) else cs t)),
        digB W (S.map fun t => if p t then u ^ e * ts t else ts t)⟩ := by
  have hblk : ∀ t ∈ S, blkF W (cs t) < 2 ^ (8 * W) := fun t ht => blkF_lt W _ (hcs t ht)
  have hsel : digB (8 * W) (S.map fun t => blkF W (cs t)) &&& selMask (8 * W) S p =
      digB (8 * W) (S.map fun t => if p t then blkF W (cs t) else 0) :=
    digB_map_select _ S _ p hblk
  have hselT : digB W (S.map ts) &&& selMask W S p =
      digB W (S.map fun t => if p t then ts t else 0) :=
    digB_map_select _ S _ p hts
  have hv : digB (8 * W) (S.map fun t => if p t then blkF W (cs t) else 0) &&&
      digB (8 * W) (S.map fun _ => 2 ^ W - 1) =
      digB (8 * W) (S.map fun t => if p t then cs t 0 else 0) := by
    rw [digB_map_and _ S _ _ (fun t ht => by split_ifs; exacts [hblk t ht, Nat.two_pow_pos _])
      (fun t _ => by
        have : 2 ^ W ≤ 2 ^ (8 * W) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have := Nat.two_pow_pos W
        omega)]
    refine digB_map_congr _ fun t ht => ?_
    split_ifs
    · rw [Nat.and_two_pow_sub_one_eq_mod, blkF_mod W _ (hcs t ht 0 (by norm_num))]
    · exact Nat.zero_and _
  have hsh : ∀ x n : ℕ, Nat.shiftLeft x n = x * 2 ^ n := fun x n => Nat.shiftLeft_eq x n
  simp only [grpStep, Nat.land_eq, hsel, hselT, hv, Nat.sub_eq, Nat.add_eq, Nat.mul_eq,
    Nat.pow_eq, hsh, digB_map_mul']
  congr 1
  · rw [digB_map_split (8 * W) S p (fun t => blkF W (cs t)), Nat.add_sub_cancel_left,
      digB_map_add, digB_map_add]
    refine digB_map_congr _ fun t _ => ?_
    unfold stepCell
    split_ifs with hp
    · rw [← blkF_add, ← blkF_mul, blkF_single W _ (k + 1) hk]
      ring
    · simp
  · rw [digB_map_split W S p ts, Nat.add_sub_cancel_left, digB_map_add]
    refine digB_map_congr _ fun t _ => ?_
    split_ifs <;> ring

end step

/-! ## Soundness: the group folds -/

section folds
variable {W : ℕ}

theorem grpR_cons (vmask sh a u : ℕ) (g : VG) (gs : List VG) (P T : ℕ) :
    grpR vmask sh a u (g :: gs) P T =
      grpR vmask sh a u gs (grpStep vmask sh a u g P T).P (grpStep vmask sh a u g P T).T := rfl

/-- The groups of one variable, for exponents `es` without repetition. -/
theorem grpR_spec (S : List Term) (x : Term → ℕ) (a u k : ℕ) (hk : k + 1 < 8)
    (es : List ℕ) (hnd : es.Nodup) : ∀ (cs : Term → ℕ → ℕ) (ts : Term → ℕ),
      (∀ t ∈ S, ∀ j < 8, cs t j < 2 ^ W ∧ (x t ∈ es → stepCell a (x t) k (cs t) j < 2 ^ W)) →
      (∀ t ∈ S, ts t < 2 ^ W ∧ (x t ∈ es → u ^ x t * ts t < 2 ^ W)) →
      grpR (digB (8 * W) (S.map fun _ => 2 ^ W - 1)) (W * (k + 1)) a u
          (es.map fun e => ⟨e, selMask (8 * W) S (fun t => x t == e),
            selMask W S (fun t => x t == e)⟩)
          (digB (8 * W) (S.map fun t => blkF W (cs t))) (digB W (S.map ts)) =
        ⟨digB (8 * W) (S.map fun t =>
            blkF W (if x t ∈ es then stepCell a (x t) k (cs t) else cs t)),
          digB W (S.map fun t => if x t ∈ es then u ^ x t * ts t else ts t)⟩ := by
  induction es with
  | nil => intro cs ts _ _; simp [grpR]
  | cons e es ih =>
      intro cs ts hc ht
      obtain ⟨he, hnd'⟩ := List.nodup_cons.mp hnd
      rw [List.map_cons, grpR_cons, grpStep_spec S _ e a u k hk cs ts
        (fun t h j hj => (hc t h j hj).1) (fun t h => (ht t h).1)]
      have key := ih hnd'
        (fun t => if (x t == e) then stepCell a e k (cs t) else cs t)
        (fun t => if (x t == e) then u ^ e * ts t else ts t)
        (fun t h j hj => by
          by_cases hx : x t = e
          · rw [ite_eq_left (beq_iff_eq.mpr hx)]
            refine ⟨?_, fun hm => absurd (hx ▸ hm) he⟩
            have := (hc t h j hj).2 (by rw [hx]; exact List.mem_cons_self)
            rwa [hx] at this
          · rw [ite_eq_right (by simpa using hx)]
            exact ⟨(hc t h j hj).1, fun hm => (hc t h j hj).2 (List.mem_cons_of_mem _ hm)⟩)
        (fun t h => by
          by_cases hx : x t = e
          · rw [ite_eq_left (beq_iff_eq.mpr hx)]
            refine ⟨?_, fun hm => absurd (hx ▸ hm) he⟩
            have := (ht t h).2 (by rw [hx]; exact List.mem_cons_self)
            rwa [hx] at this
          · rw [ite_eq_right (by simpa using hx)]
            exact ⟨(ht t h).1, fun hm => (ht t h).2 (List.mem_cons_of_mem _ hm)⟩)
      rw [key]
      have e1 : ∀ t, (if x t ∈ es then stepCell a (x t) k
            (if (x t == e) then stepCell a e k (cs t) else cs t)
          else (if (x t == e) then stepCell a e k (cs t) else cs t)) =
          if x t ∈ e :: es then stepCell a (x t) k (cs t) else cs t := by
        intro t
        by_cases hx : x t = e
        · have hn : x t ∉ es := hx ▸ he
          rw [ite_eq_right hn, ite_eq_left (beq_iff_eq.mpr hx), ite_eq_left (hx ▸ List.mem_cons_self), hx]
        · have hb : (x t == e) = false := by simpa using hx
          simp only [hb, Bool.false_eq_true, ite_false, List.mem_cons, hx, false_or]
      have e2 : ∀ t, (if x t ∈ es then u ^ x t * (if (x t == e) then u ^ e * ts t else ts t)
          else (if (x t == e) then u ^ e * ts t else ts t)) =
          if x t ∈ e :: es then u ^ x t * ts t else ts t := by
        intro t
        by_cases hx : x t = e
        · have hn : x t ∉ es := hx ▸ he
          rw [ite_eq_right hn, ite_eq_left (beq_iff_eq.mpr hx), ite_eq_left (hx ▸ List.mem_cons_self), hx]
        · have hb : (x t == e) = false := by simpa using hx
          simp only [hb, Bool.false_eq_true, ite_false, List.mem_cons, hx, false_or]
      simp only [e1, e2]

/-- The groups of `groupsOf`: every term gets its own exponent. -/
theorem grpR_groupsOf (S : List Term) (x : Term → ℕ) (a u k : ℕ) (hk : k + 1 < 8)
    (cs : Term → ℕ → ℕ) (ts : Term → ℕ)
    (hc : ∀ t ∈ S, ∀ j < 8, cs t j < 2 ^ W ∧ stepCell a (x t) k (cs t) j < 2 ^ W)
    (ht : ∀ t ∈ S, ts t < 2 ^ W ∧ u ^ x t * ts t < 2 ^ W) :
    grpR (digB (8 * W) (S.map fun _ => 2 ^ W - 1)) (W * (k + 1)) a u (groupsOf W S x)
        (digB (8 * W) (S.map fun t => blkF W (cs t))) (digB W (S.map ts)) =
      ⟨digB (8 * W) (S.map fun t => blkF W (stepCell a (x t) k (cs t))),
        digB W (S.map fun t => u ^ x t * ts t)⟩ := by
  rw [groupsOf, grpR_spec S x a u k hk _ (List.nodup_dedup _) cs ts
    (fun t h j hj => ⟨(hc t h j hj).1, fun _ => (hc t h j hj).2⟩)
    (fun t h => ⟨(ht t h).1, fun _ => (ht t h).2⟩)]
  refine congrArg₂ PP.mk ?_ ?_
  · refine digB_map_congr _ fun t h => ?_
    by_cases hx : x t = 0
    · simp [hx, stepCell_zero]
    · rw [ite_eq_left (List.mem_dedup.mpr (List.mem_filter.mpr ⟨List.mem_map_of_mem h, by simpa⟩))]
  · refine digB_map_congr _ fun t h => ?_
    by_cases hx : x t = 0
    · simp [hx]
    · rw [ite_eq_left (List.mem_dedup.mpr (List.mem_filter.mpr ⟨List.mem_map_of_mem h, by simpa⟩))]

end folds

/-! ## Soundness: all variables -/

section vars
variable {W : ℕ}

/-- A term's digits after the first `k` variables, at the point `a`. -/
def cellK (a : ℕ → ℕ) (t : Term) : ℕ → ℕ → ℕ
  | 0 => fun j => if j = 0 then t.2.1 else 0
  | k + 1 => stepCell (a k) (expAt t.1 k) k (cellK a t k)

/-- A term's majorant digit after the first `k` variables, at the point `u`. -/
def tK (u : ℕ → ℕ) (t : Term) : ℕ → ℕ
  | 0 => t.2.1
  | k + 1 => u k ^ expAt t.1 k * tK u t k

def aOf (X : List ℤ) (i : ℕ) : ℕ := (X.getD i 0).natAbs

def uOf (X H : List ℤ) (i : ℕ) : ℕ := aOf X i + (H.getD i 0).toNat

theorem headD_drop_int (l : List ℤ) (k : ℕ) : (l.drop k).headD 0 = l.getD k 0 := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih => cases k <;> simp

theorem varsR_cons (W vmask : ℕ) (gs : List VG) (vs : List (List VG)) (xs hs : List ℤ)
    (sh P T : ℕ) :
    varsR W vmask (gs :: vs) xs hs sh P T =
      varsR W vmask vs xs.tail hs.tail (Nat.add sh W)
        (grpR vmask sh (Int.natAbs (xs.headD 0))
          (Nat.add (Int.natAbs (xs.headD 0)) (Int.toNat (hs.headD 0))) gs P T).P
        (grpR vmask sh (Int.natAbs (xs.headD 0))
          (Nat.add (Int.natAbs (xs.headD 0)) (Int.toNat (hs.headD 0))) gs P T).T := rfl

theorem varsR_spec (S : List Term) (X H : List ℤ)
    (hb : ∀ t ∈ S, ∀ k ≤ 7, (∀ j < 8, cellK (aOf X) t k j < 2 ^ W) ∧ tK (uOf X H) t k < 2 ^ W) :
    ∀ n k, k + n = 7 →
      varsR W (digB (8 * W) (S.map fun _ => 2 ^ W - 1))
          ((List.range' k n).map fun i => groupsOf W S (fun t => expAt t.1 i))
          (X.drop k) (H.drop k) (W * (k + 1))
          (digB (8 * W) (S.map fun t => blkF W (cellK (aOf X) t k)))
          (digB W (S.map fun t => tK (uOf X H) t k)) =
        ⟨digB (8 * W) (S.map fun t => blkF W (cellK (aOf X) t 7)),
          digB W (S.map fun t => tK (uOf X H) t 7)⟩
  | 0, k, h => by
      obtain rfl : k = 7 := by omega
      rfl
  | n + 1, k, h => by
      rw [List.range'_succ, List.map_cons, varsR_cons, headD_drop_int, headD_drop_int,
        List.tail_drop, List.tail_drop]
      have hg := grpR_groupsOf (W := W) S (fun t => expAt t.1 k) (aOf X k) (uOf X H k) k
        (by omega) (fun t => cellK (aOf X) t k) (fun t => tK (uOf X H) t k)
        (fun t ht j hj => ⟨(hb t ht k (by omega)).1 j hj, (hb t ht (k + 1) (by omega)).1 j hj⟩)
        (fun t ht => ⟨(hb t ht k (by omega)).2, (hb t ht (k + 1) (by omega)).2⟩)
      have e1 : Nat.add (Int.natAbs (X.getD k 0)) (Int.toNat (H.getD k 0)) = uOf X H k := rfl
      have e2 : Int.natAbs (X.getD k 0) = aOf X k := rfl
      rw [e1, e2, hg]
      have e3 : Nat.add (W * (k + 1)) W = W * (k + 1 + 1) := by simp only [Nat.add_eq]; ring
      rw [e3]
      exact varsR_spec S X H hb n (k + 1) (by omega)

end vars

/-! ## Soundness: the powers of `D` -/

section powD
variable {W : ℕ}

theorem grpD_cons (D : ℕ) (g : VG) (gs : List VG) (P T : ℕ) :
    grpD D (g :: gs) P T = grpD D gs
      (Nat.add (Nat.sub P (Nat.land P g.mask)) (Nat.mul (Nat.land P g.mask) (Nat.pow D g.e)))
      (Nat.add (Nat.sub T (Nat.land T g.maskT)) (Nat.mul (Nat.land T g.maskT) (Nat.pow D g.e))) :=
  rfl

theorem grpD_spec (S : List Term) (x : Term → ℕ) (D : ℕ) (es : List ℕ) (hnd : es.Nodup) :
    ∀ (cs : Term → ℕ → ℕ) (ts : Term → ℕ),
      (∀ t ∈ S, ∀ j < 8, cs t j < 2 ^ W ∧ (x t ∈ es → D ^ x t * cs t j < 2 ^ W)) →
      (∀ t ∈ S, ts t < 2 ^ W ∧ (x t ∈ es → D ^ x t * ts t < 2 ^ W)) →
      grpD D (es.map fun e => ⟨e, selMask (8 * W) S (fun t => x t == e),
            selMask W S (fun t => x t == e)⟩)
          (digB (8 * W) (S.map fun t => blkF W (cs t))) (digB W (S.map ts)) =
        ⟨digB (8 * W) (S.map fun t =>
            blkF W (if x t ∈ es then (fun j => D ^ x t * cs t j) else cs t)),
          digB W (S.map fun t => if x t ∈ es then D ^ x t * ts t else ts t)⟩ := by
  induction es with
  | nil => intro cs ts _ _; simp [grpD]
  | cons e es ih =>
      intro cs ts hc ht
      obtain ⟨he, hnd'⟩ := List.nodup_cons.mp hnd
      have hblk : ∀ t ∈ S, blkF W (cs t) < 2 ^ (8 * W) := fun t h =>
        blkF_lt W _ fun j hj => (hc t h j hj).1
      rw [List.map_cons, grpD_cons]
      simp only [Nat.land_eq, Nat.sub_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq]
      rw [selMask, digB_map_select _ S _ _ hblk, selMask, digB_map_select _ S _ _ (fun t h => (ht t h).1),
        digB_map_split (8 * W) S (fun t => x t == e) (fun t => blkF W (cs t)),
        Nat.add_sub_cancel_left, digB_map_split W S (fun t => x t == e) ts,
        Nat.add_sub_cancel_left, digB_map_mul', digB_map_mul', digB_map_add, digB_map_add]
      have key := ih hnd' (fun t => if (x t == e) then (fun j => D ^ e * cs t j) else cs t)
        (fun t => if (x t == e) then D ^ e * ts t else ts t) ?_ ?_
      · rw [show (fun t => (if (x t == e) = true then 0 else blkF W (cs t)) +
              (if (x t == e) = true then blkF W (cs t) else 0) * D ^ e) =
            fun t => blkF W (if (x t == e) then (fun j => D ^ e * cs t j) else cs t) by
            funext t; split_ifs <;> simp [blkF_mul, Nat.mul_comm],
          show (fun t => (if (x t == e) = true then 0 else ts t) +
              (if (x t == e) = true then ts t else 0) * D ^ e) =
            fun t => if (x t == e) then D ^ e * ts t else ts t by
            funext t; split_ifs <;> simp [Nat.mul_comm], key]
        refine congrArg₂ PP.mk (digB_map_congr _ fun t _ => ?_) (digB_map_congr _ fun t _ => ?_)
        · by_cases hx : x t = e
          · have hn : x t ∉ es := hx ▸ he
            rw [ite_eq_right hn, ite_eq_left (beq_iff_eq.mpr hx), ite_eq_left (hx ▸ List.mem_cons_self), hx]
          · have hb : (x t == e) = false := by simpa using hx
            simp only [hb, Bool.false_eq_true, ite_false, List.mem_cons, hx, false_or]
        · by_cases hx : x t = e
          · have hn : x t ∉ es := hx ▸ he
            rw [ite_eq_right hn, ite_eq_left (beq_iff_eq.mpr hx), ite_eq_left (hx ▸ List.mem_cons_self), hx]
          · have hb : (x t == e) = false := by simpa using hx
            simp only [hb, Bool.false_eq_true, ite_false, List.mem_cons, hx, false_or]
      · intro t h j hj
        by_cases hx : x t = e
        · rw [ite_eq_left (beq_iff_eq.mpr hx)]
          refine ⟨?_, fun hm => absurd (hx ▸ hm) he⟩
          have := (hc t h j hj).2 (by rw [hx]; exact List.mem_cons_self)
          rwa [hx] at this
        · rw [ite_eq_right (by simpa using hx)]
          exact ⟨(hc t h j hj).1, fun hm => (hc t h j hj).2 (List.mem_cons_of_mem _ hm)⟩
      · intro t h
        by_cases hx : x t = e
        · rw [ite_eq_left (beq_iff_eq.mpr hx)]
          refine ⟨?_, fun hm => absurd (hx ▸ hm) he⟩
          have := (ht t h).2 (by rw [hx]; exact List.mem_cons_self)
          rwa [hx] at this
        · rw [ite_eq_right (by simpa using hx)]
          exact ⟨(ht t h).1, fun hm => (ht t h).2 (List.mem_cons_of_mem _ hm)⟩

theorem grpD_groupsOf (S : List Term) (x : Term → ℕ) (D : ℕ)
    (cs : Term → ℕ → ℕ) (ts : Term → ℕ)
    (hc : ∀ t ∈ S, ∀ j < 8, cs t j < 2 ^ W ∧ D ^ x t * cs t j < 2 ^ W)
    (ht : ∀ t ∈ S, ts t < 2 ^ W ∧ D ^ x t * ts t < 2 ^ W) :
    grpD D (groupsOf W S x) (digB (8 * W) (S.map fun t => blkF W (cs t))) (digB W (S.map ts)) =
      ⟨digB (8 * W) (S.map fun t => blkF W (fun j => D ^ x t * cs t j)),
        digB W (S.map fun t => D ^ x t * ts t)⟩ := by
  rw [groupsOf, grpD_spec S x D _ (List.nodup_dedup _) cs ts
    (fun t h j hj => ⟨(hc t h j hj).1, fun _ => (hc t h j hj).2⟩)
    (fun t h => ⟨(ht t h).1, fun _ => (ht t h).2⟩)]
  refine congrArg₂ PP.mk (digB_map_congr _ fun t h => ?_) (digB_map_congr _ fun t h => ?_)
  · by_cases hx : x t = 0
    · simp [hx]
    · rw [ite_eq_left (List.mem_dedup.mpr (List.mem_filter.mpr ⟨List.mem_map_of_mem h, by simpa⟩))]
  · by_cases hx : x t = 0
    · simp [hx]
    · rw [ite_eq_left (List.mem_dedup.mpr (List.mem_filter.mpr ⟨List.mem_map_of_mem h, by simpa⟩))]

end powD

/-! ## Soundness: closed forms -/

section closed

/-- `∏ᵢ<k aᵢ^(mᵢ)`. -/
def prK (a : ℕ → ℕ) (m : Mono) (k : ℕ) : ℕ := ∏ i ∈ Finset.range k, a i ^ expAt m i

/-- The same product with the exponent of `j` lowered by one. -/
def dprK (a : ℕ → ℕ) (m : Mono) (k j : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, if i = j then a i ^ (expAt m i - 1) else a i ^ expAt m i

theorem cellK_zero (a : ℕ → ℕ) (t : Term) : ∀ k, cellK a t k 0 = t.2.1 * prK a t.1 k
  | 0 => by simp [cellK, prK]
  | k + 1 => by
      simp only [cellK, stepCell, cellK_zero a t k, prK, Finset.prod_range_succ]
      simp only [ite_false, add_zero, show (0 : ℕ) ≠ k + 1 by omega]
      ring

theorem cellK_succ (a : ℕ → ℕ) (t : Term) : ∀ k j, cellK a t k (j + 1) =
    if j < k then t.2.1 * expAt t.1 j * dprK a t.1 k j else 0
  | 0, j => by simp [cellK]
  | k + 1, j => by
      show stepCell (a k) (expAt t.1 k) k (cellK a t k) (j + 1) = _
      unfold stepCell
      rw [cellK_succ a t k j, cellK_zero]
      rcases lt_trichotomy j k with hjk | hjk | hjk
      · simp only [hjk, ite_true, show j + 1 ≠ k + 1 by omega, ite_false, add_zero,
          show j < k + 1 by omega, dprK, Finset.prod_range_succ, show k ≠ j by omega]
        ring
      · subst hjk
        simp only [lt_irrefl, ite_false, mul_zero, zero_add, ite_true, Nat.lt_succ_self, dprK,
          Finset.prod_range_succ, prK]
        rw [Finset.prod_congr rfl fun i hi => (show (if i = j then a i ^ (expAt t.1 i - 1)
            else a i ^ expAt t.1 i) = a i ^ expAt t.1 i by
          rw [Finset.mem_range] at hi; simp [show i ≠ j by omega])]
        ring
      · simp only [show ¬ j < k by omega, ite_false, show j + 1 ≠ k + 1 by omega,
          show ¬ j < k + 1 by omega]
        simp

theorem tK_eq (u : ℕ → ℕ) (t : Term) : ∀ k, tK u t k = t.2.1 * prK u t.1 k
  | 0 => by simp [tK, prK]
  | k + 1 => by simp only [tK, tK_eq u t k, prK, Finset.prod_range_succ]; ring

theorem expAt_cons_zero (e : ℕ) (m : Mono) : expAt (e :: m) 0 = e := rfl

theorem expAt_cons_succ (e : ℕ) (m : Mono) (i : ℕ) : expAt (e :: m) (i + 1) = expAt m i := rfl

theorem expAt_of_le (m : Mono) (i : ℕ) (h : m.length ≤ i) : expAt m i = 0 := by
  simp [expAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_drop_nat (l : List ℕ) (k i : ℕ) : (l.drop k).getD i 0 = l.getD (k + i) 0 := by
  simp [List.getD_eq_getElem?_getD]

theorem monoNat_prod (ax : List ℕ) : ∀ (m : Mono) (k n : ℕ), m.length ≤ n →
    monoNat (ax.drop k) m = ∏ i ∈ Finset.range n, ax.getD (k + i) 0 ^ expAt m i
  | [], k, n, _ => by simp [monoNat, expAt]
  | e :: m, k, n + 1, h => by
      simp only [List.length_cons] at h
      rw [Finset.prod_range_succ', monoNat, List.tail_drop, monoNat_prod ax m (k + 1) n (by omega),
        headD_drop]
      simp only [expAt_cons_zero, expAt_cons_succ, add_zero]
      rw [Nat.mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [show k + (i + 1) = k + 1 + i by ring]
  | _ :: _, _, 0, h => absurd h (by simp)

theorem derivN_prod (ax : List ℕ) (j : ℕ) : ∀ (m : Mono) (k n : ℕ), m.length ≤ n →
    derivN ax j k m = if k ≤ j then expAt m (j - k) * ∏ i ∈ Finset.range n,
      (if k + i = j then ax.getD (k + i) 0 ^ (expAt m i - 1) else ax.getD (k + i) 0 ^ expAt m i)
      else 0
  | [], k, n, _ => by simp [derivN, expAt]
  | e :: m, k, n + 1, h => by
      simp only [List.length_cons] at h
      rw [derivN, Finset.prod_range_succ']
      rcases lt_trichotomy k j with hkj | hkj | hkj
      · rw [ite_eq_right (by omega), derivN_prod ax j m (k + 1) n (by omega), ite_eq_left (by omega),
          ite_eq_left (by omega)]
        simp only [add_zero, show k ≠ j by omega, ite_false, expAt_cons_succ]
        rw [show j - k = (j - (k + 1)) + 1 by omega, expAt_cons_succ]
        have : ∀ i ∈ Finset.range n, (if k + (i + 1) = j then ax.getD (k + (i + 1)) 0 ^
              (expAt m i - 1) else ax.getD (k + (i + 1)) 0 ^ expAt m i) =
            if k + 1 + i = j then ax.getD (k + 1 + i) 0 ^ (expAt m i - 1)
              else ax.getD (k + 1 + i) 0 ^ expAt m i := fun i _ => by
          rw [show k + (i + 1) = k + 1 + i by ring]
        rw [Finset.prod_congr rfl this, expAt_cons_zero]
        ring
      · subst hkj
        rw [ite_eq_left rfl, ite_eq_left le_rfl, monoNat_prod ax m (k + 1) n (by omega)]
        simp only [Nat.sub_self, expAt_cons_zero, add_zero, ite_true]
        have : ∀ i ∈ Finset.range n, (if k + (i + 1) = k then ax.getD (k + (i + 1)) 0 ^
              (expAt (e :: m) (i + 1) - 1) else ax.getD (k + (i + 1)) 0 ^ expAt (e :: m) (i + 1)) =
            ax.getD (k + 1 + i) 0 ^ expAt m i := fun i _ => by
          rw [ite_eq_right (by omega), show k + (i + 1) = k + 1 + i by ring, expAt_cons_succ]
        rw [Finset.prod_congr rfl this]
        ring
      · rw [ite_eq_right (by omega), derivN_prod ax j m (k + 1) n (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), mul_zero]
  | _ :: _, _, 0, h => absurd h (by simp)

end closed

/-! ## Soundness: signs, the linear part, the bound -/

section misc

theorem selMask_xor (B : ℕ) (S : List Term) (p q : Term → Bool) :
    selMask B S p ^^^ selMask B S q = selMask B S (fun t => p t ^^ q t) := by
  have hb : ∀ (r : Term → Bool), ∀ t ∈ S, (if r t then 2 ^ B - 1 else 0) < 2 ^ B := by
    intro r t _; have := Nat.two_pow_pos B; split_ifs <;> omega
  rw [selMask, selMask, digB_map_xor B S _ _ (hb p) (hb q), selMask]
  refine digB_map_congr B fun t _ => ?_
  cases p t <;> cases q t <;> simp

theorem isNegI_eq (x : ℤ) : isNegI x = decide (x < 0) := by
  cases x with
  | ofNat n => simp [isNegI]
  | negSucc n => simp [isNegI, Int.negSucc_lt_zero]

/-- The parity of the negative factors among variables `k, …, k + n - 1`. -/
def parR (X : List ℤ) (m : Mono) : ℕ → ℕ → Bool
  | _, 0 => false
  | k, n + 1 => (isNegI (X.getD k 0) && expAt m k % 2 == 1) ^^ parR X m (k + 1) n

theorem negR_cons (o : ℕ) (os : List ℕ) (xs : List ℤ) (acc : ℕ) :
    negR (o :: os) xs acc = negR os xs.tail (cond (isNegI (xs.headD 0)) (Nat.xor acc o) acc) :=
  rfl

theorem negR_spec (B : ℕ) (S : List Term) (X : List ℤ) : ∀ (n k : ℕ) (p : Term → Bool),
    negR ((List.range' k n).map fun i => selMask B S (fun t => expAt t.1 i % 2 == 1))
        (X.drop k) (selMask B S p) = selMask B S (fun t => p t ^^ parR X t.1 k n)
  | 0, k, p => by simp [negR, parR]
  | n + 1, k, p => by
      rw [List.range'_succ, List.map_cons, negR_cons, headD_drop_int, List.tail_drop]
      cases hneg : isNegI (X.getD k 0)
      · simp only [Bool.cond_false]
        rw [negR_spec B S X n (k + 1) p]
        congr 1
        funext t
        simp only [parR, hneg, Bool.false_and, Bool.false_xor]
      · simp only [Bool.cond_true]
        rw [Nat.xor_eq, selMask_xor, negR_spec B S X n (k + 1)]
        congr 1
        funext t
        simp only [parR, hneg, Bool.true_and, Bool.xor_assoc]

theorem parN_eq_parR (X : List ℤ) (m : Mono) : ∀ (n k : ℕ), m.length ≤ k + n →
    parN ((X.map fun x => decide (x < 0)).drop k) (m.drop k) = parR X m k n
  | 0, k, h => by
      rw [List.drop_eq_nil_of_le (as := m) (by omega)]
      rfl
  | n + 1, k, h => by
      have ih := parN_eq_parR X m n (k + 1) (by omega)
      have hhead : ((X.map fun x => decide (x < 0)).drop k).headD false =
          isNegI (X.getD k 0) := by
        rw [isNegI_eq]
        rcases Nat.lt_or_ge k X.length with hk | hk
        · simp [List.getD_eq_getElem?_getD, hk, List.headD_eq_head?_getD]
        · simp [List.getD_eq_getElem?_getD, List.drop_eq_nil_of_le, hk]
      rcases Nat.lt_or_ge k m.length with hk | hk
      · have hm : m.drop k = expAt m k :: m.drop (k + 1) := by
          rw [List.drop_eq_getElem_cons hk]
          simp [expAt, List.getD_eq_getElem?_getD, hk]
        rw [hm, parN, List.tail_drop, ih, parR, hhead]
      · rw [List.drop_eq_nil_of_le (as := m) (by omega)] at ih
        rw [List.drop_eq_nil_of_le (as := m) hk, parR, expAt_of_le m k hk, ← ih]
        simp [parN]

theorem linR_cons (W wmask sp sn : ℕ) (h : ℤ) (hs : List ℤ) (sh lin L : ℕ) :
    linR W wmask sp sn (h :: hs) sh lin L =
      linR W wmask sp sn hs (Nat.add sh W)
        (Nat.add lin (Nat.mul (Int.toNat h) (cond (Nat.ble (Nat.land (Nat.shiftRight sp sh) wmask)
            (Nat.land (Nat.shiftRight sn sh) wmask))
          (Nat.sub (Nat.land (Nat.shiftRight sn sh) wmask) (Nat.land (Nat.shiftRight sp sh) wmask))
          (Nat.sub (Nat.land (Nat.shiftRight sp sh) wmask) (Nat.land (Nat.shiftRight sn sh) wmask)))))
        (Nat.add L (Nat.mul (Int.toNat h) (Nat.add (Nat.land (Nat.shiftRight sp sh) wmask)
          (Nat.land (Nat.shiftRight sn sh) wmask)))) := rfl

/-- Digit `j + 1` (the derivative in variable `j`) of a summed block. -/
def dgt (W x j : ℕ) : ℕ := Nat.land (Nat.shiftRight x (W * (j + 1))) (2 ^ W - 1)

theorem linR_spec (W sp sn : ℕ) : ∀ (l : List ℤ) (k lin L : ℕ),
    linR W (2 ^ W - 1) sp sn l (W * (k + 1)) lin L =
      ⟨lin + ∑ i ∈ Finset.range l.length,
          (l.getD i 0).toNat * linT true (dgt W sp (k + i)) (dgt W sn (k + i)),
        L + ∑ i ∈ Finset.range l.length,
          (l.getD i 0).toNat * (dgt W sp (k + i) + dgt W sn (k + i))⟩
  | [], k, lin, L => by simp [linR]
  | h :: l, k, lin, L => by
      rw [linR_cons, show Nat.add (W * (k + 1)) W = W * (k + 1 + 1) by simp only [Nat.add_eq]; ring,
        linR_spec W sp sn l (k + 1)]
      simp only [List.length_cons, Finset.sum_range_succ', List.getD_cons_succ,
        List.getD_cons_zero, add_zero]
      have hlin : ∀ p q : ℕ, cond (Nat.ble p q) (Nat.sub q p) (Nat.sub p q) = linT true p q := by
        intro p q
        unfold linT
        by_cases hpq : p ≤ q
        · have hb : Nat.ble p q = true := by rw [Nat.ble_eq]; exact hpq
          simp [hb, hpq]
        · have hb : Nat.ble p q = false := by rw [← Bool.not_eq_true, Nat.ble_eq]; exact hpq
          simp [hb, hpq]
      rw [hlin]
      have e : ∀ i, k + 1 + i = k + (i + 1) := fun i => by ring
      refine congrArg₂ LL.mk ?_ ?_
      · simp only [e, Nat.add_eq, Nat.mul_eq]
        rw [show (sp.shiftRight (W * (k + 1))).land (2 ^ W - 1) = dgt W sp k from rfl,
          show (sn.shiftRight (W * (k + 1))).land (2 ^ W - 1) = dgt W sn k from rfl]
        ring
      · simp only [e, Nat.add_eq, Nat.mul_eq]
        rw [show (sp.shiftRight (W * (k + 1))).land (2 ^ W - 1) = dgt W sp k from rfl,
          show (sn.shiftRight (W * (k + 1))).land (2 ^ W - 1) = dgt W sn k from rfl]
        ring

theorem maxR_ge (D : ℕ) : ∀ (X H : List ℤ), H.length ≤ X.length →
    D ≤ maxR D X H ∧ ∀ i, aOf X i ≤ maxR D X H ∧ uOf X H i ≤ maxR D X H
  | [], H, h => by
      have : H = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp h)
      subst this
      refine ⟨le_rfl, fun i => ?_⟩
      simp [aOf, uOf, maxR]
  | x :: X, H, h => by
      have ih := maxR_ge D X H.tail (by simp; omega)
      have e : maxR D (x :: X) H = Nat.max (x.natAbs + (H.headD 0).toNat) (maxR D X H.tail) := rfl
      rw [e]
      refine ⟨le_trans ih.1 (Nat.le_max_right _ _), fun i => ?_⟩
      cases i with
      | zero =>
          have hu : uOf (x :: X) H 0 = x.natAbs + (H.headD 0).toNat := by
            cases H <;> simp [uOf, aOf]
          simp only [hu, aOf, List.getD_cons_zero]
          exact ⟨le_trans (Nat.le_add_right _ _) (Nat.le_max_left _ _), Nat.le_max_left _ _⟩
      | succ i =>
          have hu : uOf (x :: X) H (i + 1) = uOf X H.tail i := by
            cases H <;> simp [uOf, aOf]
          have ha : aOf (x :: X) (i + 1) = aOf X i := by simp [aOf]
          rw [hu, ha]
          exact ⟨le_trans (ih.2 i).1 (Nat.le_max_right _ _),
            le_trans (ih.2 i).2 (Nat.le_max_right _ _)⟩

end misc

/-! ## Soundness: digit bounds -/

section bounds

theorem sum_expAt_le : ∀ (m : Mono) (k : ℕ), ∑ i ∈ Finset.range k, expAt m i ≤ degM m
  | [], k => by simp [expAt]
  | e :: m, 0 => by simp
  | e :: m, k + 1 => by
      rw [Finset.sum_range_succ', degM_cons]
      simp only [expAt_cons_succ, expAt_cons_zero]
      have := sum_expAt_le m k
      omega

theorem sum_expAt_eq : ∀ (m : Mono) (k : ℕ), m.length ≤ k →
    ∑ i ∈ Finset.range k, expAt m i = degM m
  | [], k, _ => by simp [expAt, degM]
  | e :: m, 0, h => absurd h (by simp)
  | e :: m, k + 1, h => by
      simp only [List.length_cons] at h
      rw [Finset.sum_range_succ', degM_cons]
      simp only [expAt_cons_succ, expAt_cons_zero]
      rw [sum_expAt_eq m k (by omega)]
      ring

theorem expAt_le_degM : ∀ (m : Mono) (i : ℕ), expAt m i ≤ degM m
  | [], i => by simp [expAt]
  | e :: m, 0 => by simp [expAt_cons_zero, degM_cons]
  | e :: m, i + 1 => by
      rw [expAt_cons_succ, degM_cons]
      have := expAt_le_degM m i
      omega

variable {a : ℕ → ℕ} {M : ℕ} (ha : ∀ i, a i ≤ M) (hM : 1 ≤ M)
include ha

theorem prK_le (m : Mono) (k : ℕ) : prK a m k ≤ M ^ ∑ i ∈ Finset.range k, expAt m i := by
  rw [prK, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod fun i _ => Nat.pow_le_pow_left (ha i) _

include hM

theorem dprK_le (m : Mono) (k j : ℕ) : dprK a m k j ≤ M ^ ∑ i ∈ Finset.range k, expAt m i := by
  rw [dprK, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod fun i _ => ?_
  split_ifs
  · exact le_trans (Nat.pow_le_pow_left (ha i) _) (Nat.pow_le_pow_right hM (Nat.sub_le _ _))
  · exact Nat.pow_le_pow_left (ha i) _

/-- Every digit of a term after `k ≤ 7` variables, scaled by `s`, is at most
`c (N + 1) M^N` when `s M^(deg) ≤ M^N`. -/
theorem cellK_le (t : Term) (N s k : ℕ) (hdeg : degM t.1 ≤ N)
    (hs : s * M ^ degM t.1 ≤ M ^ N) (j : ℕ) (hj : j < 8) :
    s * cellK a t k j ≤ t.2.1 * ((N + 1) * M ^ N) := by
  have hpow : s * M ^ (∑ i ∈ Finset.range k, expAt t.1 i) ≤ M ^ N :=
    le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hM (sum_expAt_le t.1 k))) hs
  rcases j with _ | j
  · rw [cellK_zero]
    calc s * (t.2.1 * prK a t.1 k) = t.2.1 * (s * prK a t.1 k) := by ring
      _ ≤ t.2.1 * (s * M ^ ∑ i ∈ Finset.range k, expAt t.1 i) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (prK_le ha t.1 k))
      _ ≤ t.2.1 * M ^ N := Nat.mul_le_mul_left _ hpow
      _ ≤ t.2.1 * ((N + 1) * M ^ N) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  · rw [cellK_succ]
    split_ifs
    · calc s * (t.2.1 * expAt t.1 j * dprK a t.1 k j)
          = t.2.1 * (expAt t.1 j * (s * dprK a t.1 k j)) := by ring
        _ ≤ t.2.1 * ((N + 1) * M ^ N) := by
          refine Nat.mul_le_mul_left _ (Nat.mul_le_mul (by have := expAt_le_degM t.1 j; omega) ?_)
          exact le_trans (Nat.mul_le_mul_left _ (dprK_le ha hM t.1 k j)) hpow
    · simp

theorem tK_le (t : Term) (N s k : ℕ) (hs : s * M ^ degM t.1 ≤ M ^ N) :
    s * tK a t k ≤ t.2.1 * ((N + 1) * M ^ N) := by
  rw [tK_eq]
  calc s * (t.2.1 * prK a t.1 k) = t.2.1 * (s * prK a t.1 k) := by ring
    _ ≤ t.2.1 * (s * M ^ ∑ i ∈ Finset.range k, expAt t.1 i) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (prK_le ha t.1 k))
    _ ≤ t.2.1 * M ^ N := Nat.mul_le_mul_left _
        (le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hM (sum_expAt_le t.1 k))) hs)
    _ ≤ t.2.1 * ((N + 1) * M ^ N) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))

end bounds

theorem list_sum_le {α : Type*} (L : List α) (f g : α → ℕ) (h : ∀ t ∈ L, f t ≤ g t) :
    (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons t L ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h t List.mem_cons_self) (ih fun u hu => h u (List.mem_cons_of_mem _ hu))

theorem list_sum_mul {α : Type*} (L : List α) (f : α → ℕ) (K : ℕ) :
    (L.map fun t => f t * K).sum = (L.map f).sum * K := by
  induction L with
  | nil => simp
  | cons t L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem le_list_sum {α : Type*} (L : List α) (f : α → ℕ) (t : α) (ht : t ∈ L) :
    f t ≤ (L.map f).sum := by
  induction L with
  | nil => simp at ht
  | cons u L ih =>
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp ht with rfl | h
      · omega
      · have := ih h; omega

theorem blkF_lt_sub_one (W : ℕ) (c : ℕ → ℕ) (h0 : c 0 < 2 ^ W - 1) (hc : ∀ j < 8, c j < 2 ^ W) :
    blkF W c < 2 ^ (8 * W) - 1 := by
  have hR := digB_lt W (List.range' 1 7) c (fun j hj => hc j (by
    rw [List.mem_range'] at hj; omega))
  simp only [List.length_range'] at hR
  have e : blkF W c = c 0 + 2 ^ W * digB W ((List.range' 1 7).map c) := by
    rw [blkF, List.range_eq_range', List.range'_succ, List.map_cons, digB_cons]
  rw [e]
  have h8 : 2 ^ (8 * W) = 2 ^ W * 2 ^ (W * 7) := by rw [← pow_add]; ring_nf
  have : 2 ^ W * digB W ((List.range' 1 7).map c) ≤ 2 ^ W * (2 ^ (W * 7) - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hp := Nat.one_le_two_pow (n := W * 7)
  rw [h8]
  have : 2 ^ W * (2 ^ (W * 7) - 1) = 2 ^ W * 2 ^ (W * 7) - 2 ^ W := by
    rw [Nat.mul_sub, mul_one]
  have := Nat.one_le_two_pow (n := W)
  have : 2 ^ W ≤ 2 ^ W * 2 ^ (W * 7) := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-! ## Soundness: the implication -/

theorem getD_map_natAbs (X : List ℤ) (i : ℕ) : (X.map Int.natAbs).getD i 0 = aOf X i := by
  simp [aOf, List.getD_eq_getElem?_getD]
  cases X[i]? <;> rfl

theorem getD_map_toNat (H : List ℤ) (i : ℕ) : (H.map Int.toNat).getD i 0 = (H.getD i 0).toNat := by
  simp [List.getD_eq_getElem?_getD]
  cases H[i]? <;> rfl

/-- `pSlot` pairs, by the sign of the coordinate. -/
theorem pSlot_pair (D N : ℕ) (ax : List ℕ) (sgB : List Bool) (Hn : List ℕ) (S : List Term) (j : ℕ) :
    let dP := (S.map fun t => if tneg sgB t then 0 else tc D N t * derivN ax j 0 t.1).sum
    let dN := (S.map fun t => if tneg sgB t then tc D N t * derivN ax j 0 t.1 else 0).sum
    linT true (pSlot D N ax sgB Hn S true j) (pSlot D N ax sgB Hn S false j) =
        Hn.getD j 0 * linT true dP dN ∧
      pSlot D N ax sgB Hn S true j + pSlot D N ax sgB Hn S false j = Hn.getD j 0 * (dP + dN) := by
  intro dP dN
  have hP : (S.map fun t => if (sgB.getD j false == tneg sgB t) == (!sgB.getD j false) then
      tc D N t * (Hn.getD j 0 * derivN ax j 0 t.1) else 0).sum = Hn.getD j 0 * dP := by
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
    cases sgB.getD j false <;> cases tneg sgB t <;> simp <;> ring
  have hN : (S.map fun t => if (sgB.getD j false == tneg sgB t) == (sgB.getD j false) then
      tc D N t * (Hn.getD j 0 * derivN ax j 0 t.1) else 0).sum = Hn.getD j 0 * dN := by
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
    cases sgB.getD j false <;> cases tneg sgB t <;> simp <;> ring
  have hlin : ∀ h p q : ℕ, linT true (h * p) (h * q) = h * linT true p q := by
    intro h p q
    simp only [linT, ite_true]
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · simp
    · by_cases hpq : p ≤ q
      · rw [ite_eq_left (Nat.mul_le_mul_left _ hpq), ite_eq_left hpq, Nat.mul_sub]
      · rw [ite_eq_right (fun h' => hpq (Nat.le_of_mul_le_mul_left h' hh)), ite_eq_right hpq,
          Nat.mul_sub]
  have hsym : ∀ p q : ℕ, linT true p q = linT true q p := by
    intro p q; simp only [linT, ite_true]; split_ifs <;> omega
  unfold pSlot
  cases hs : sgB.getD j false
  · simp only [hs, Bool.not_false] at hP hN
    rw [hP, hN, hlin]
    exact ⟨rfl, by ring⟩
  · simp only [hs, Bool.not_true] at hP hN
    rw [hP, hN, hsym, hlin]
    exact ⟨rfl, by ring⟩

theorem cheapS_imp (W : ℕ) (fp : FactPoly) (D : ℕ) (X H : List ℤ) (hX : X.length ≤ 7)
    (hHX : H.length ≤ X.length) (h : cheapS (mkPFP W fp) D X H = true) :
    cheapI (toIPoly fp.S) D (xI (X.map Int.natAbs) (X.map fun x => decide (x < 0)))
      (loI (H.map Int.toNat) true) (natI (H.map Int.toNat)) = true := by
  have hW : (mkPFP W fp).W = W := rfl
  have hN : (mkPFP W fp).N = maxDegN fp.S := rfl
  have hcs : (mkPFP W fp).csum = (fp.S.map fun t => t.2.1).sum := rfl
  have hsok : (mkPFP W fp).sok = fp.S.all fun t => decide (t.1.length ≤ 7) := rfl
  have hC : (mkPFP W fp).C = digB (8 * W) (fp.S.map fun t => t.2.1) := rfl
  have hCT : (mkPFP W fp).CT = digB W (fp.S.map fun t => t.2.1) := rfl
  have hvars : (mkPFP W fp).vars =
      (List.range 7).map fun i => groupsOf W fp.S (fun t => expAt t.1 i) := rfl
  have hdg : (mkPFP W fp).dg = groupsOf W fp.S (fun t => maxDegN fp.S - degM t.1) := rfl
  have hCS : (mkPFP W fp).CS = selMask (8 * W) fp.S (fun t => t.2.2) := rfl
  have hodd : (mkPFP W fp).odd =
      (List.range 7).map fun i => selMask (8 * W) fp.S (fun t => expAt t.1 i % 2 == 1) := rfl
  have hvm : (mkPFP W fp).vmask = digB (8 * W) (fp.S.map fun _ => 2 ^ W - 1) := rfl
  have hwm : (mkPFP W fp).wmask = 2 ^ W - 1 := rfl
  have hbm : (mkPFP W fp).bmod = 2 ^ (8 * W) - 1 := rfl
  simp only [cheapS, hW, hN, hcs, hsok, hC, hCT, hvars, hdg, hCS, hodd, hvm, hwm, hbm,
    Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hS, hD⟩, hguard⟩, hfin⟩ := h
  set S := fp.S with hSdef
  set N := maxDegN S with hNdef
  set M := maxR D X H with hMdef
  have hMge := maxR_ge D X H hHX
  have hM1 : 1 ≤ M := le_trans hD hMge.1
  have ha : ∀ i, aOf X i ≤ M := fun i => (hMge.2 i).1
  have hu : ∀ i, uOf X H i ≤ M := fun i => (hMge.2 i).2
  have hdeg : ∀ t ∈ S, degM t.1 ≤ N := fun t ht => degM_le_maxDegN S t ht
  set csum := (S.map fun t => t.2.1).sum with hcsdef
  have hc : ∀ t ∈ S, t.2.1 ≤ csum := fun t ht => le_list_sum S (fun t => t.2.1) t ht
  have hG : csum * ((N + 1) * M ^ N) < 2 ^ W - 1 := by
    have : (csum.mul N.succ).mul (M.pow N) = csum * ((N + 1) * M ^ N) := by
      simp only [Nat.mul_eq, Nat.pow_eq, Nat.succ_eq_add_one]; ring
    rwa [this] at hguard
  have hdig : ∀ t ∈ S, t.2.1 * ((N + 1) * M ^ N) < 2 ^ W - 1 := fun t ht =>
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (hc t ht)) hG
  have hb : ∀ t ∈ S, ∀ k ≤ 7, (∀ j < 8, cellK (aOf X) t k j < 2 ^ W) ∧
      tK (uOf X H) t k < 2 ^ W := by
    intro t ht k _
    have hs1 : 1 * M ^ degM t.1 ≤ M ^ N := by
      rw [one_mul]; exact Nat.pow_le_pow_right hM1 (hdeg t ht)
    have hd := hdig t ht
    refine ⟨fun j hj => ?_, ?_⟩
    · have := cellK_le ha hM1 t N 1 k (hdeg t ht) hs1 j hj
      omega
    · have := tK_le hu hM1 t N 1 k hs1
      omega
  -- the variables
  have hr1 : varsR W (digB (8 * W) (S.map fun _ => 2 ^ W - 1))
      ((List.range 7).map fun i => groupsOf W S (fun t => expAt t.1 i)) X H W
      (digB (8 * W) (S.map fun t => t.2.1)) (digB W (S.map fun t => t.2.1)) =
      ⟨digB (8 * W) (S.map fun t => blkF W (cellK (aOf X) t 7)),
        digB W (S.map fun t => tK (uOf X H) t 7)⟩ := by
    have hC0 : digB (8 * W) (S.map fun t => t.2.1) =
        digB (8 * W) (S.map fun t => blkF W (cellK (aOf X) t 0)) :=
      digB_map_congr _ fun t _ => by
        rw [show cellK (aOf X) t 0 = fun j => if j = 0 then t.2.1 else 0 from rfl,
          blkF_single W _ 0 (by norm_num)]
        simp
    have hCT0 : digB W (S.map fun t => t.2.1) = digB W (S.map fun t => tK (uOf X H) t 0) := rfl
    rw [hC0, hCT0, List.range_eq_range']
    have := varsR_spec (W := W) S X H hb 7 0 rfl
    simpa using this
  -- the powers of `D`
  have hsD : ∀ t ∈ S, D ^ (N - degM t.1) * M ^ degM t.1 ≤ M ^ N := by
    intro t ht
    calc D ^ (N - degM t.1) * M ^ degM t.1 ≤ M ^ (N - degM t.1) * M ^ degM t.1 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hMge.1 _)
      _ = M ^ N := by rw [← pow_add, Nat.sub_add_cancel (hdeg t ht)]
  have hcD : ∀ t ∈ S, ∀ j < 8, D ^ (N - degM t.1) * cellK (aOf X) t 7 j < 2 ^ W - 1 := by
    intro t ht j hj
    have := cellK_le ha hM1 t N _ 7 (hdeg t ht) (hsD t ht) j hj
    have := hdig t ht
    omega
  have htD : ∀ t ∈ S, D ^ (N - degM t.1) * tK (uOf X H) t 7 < 2 ^ W - 1 := by
    intro t ht
    have := tK_le hu hM1 t N _ 7 (hsD t ht)
    have := hdig t ht
    omega
  have hr : grpD D (groupsOf W S fun t => N - degM t.1)
      (digB (8 * W) (S.map fun t => blkF W (cellK (aOf X) t 7)))
      (digB W (S.map fun t => tK (uOf X H) t 7)) =
      ⟨digB (8 * W) (S.map fun t => blkF W (fun j => D ^ (N - degM t.1) * cellK (aOf X) t 7 j)),
        digB W (S.map fun t => D ^ (N - degM t.1) * tK (uOf X H) t 7)⟩ :=
    grpD_groupsOf S _ D _ _
      (fun t ht j hj => ⟨(hb t ht 7 le_rfl).1 j hj, by have := hcD t ht j hj; omega⟩)
      (fun t ht => ⟨(hb t ht 7 le_rfl).2, by have := htD t ht; omega⟩)
  -- the signs
  set sgB := X.map fun x => decide (x < 0) with hsgB
  have hneg : negR ((List.range 7).map fun i => selMask (8 * W) S fun t => expAt t.1 i % 2 == 1) X
      (selMask (8 * W) S fun t => t.2.2) = selMask (8 * W) S (fun t => tneg sgB t) := by
    rw [List.range_eq_range']
    have := negR_spec (8 * W) S X 7 0 (fun t => t.2.2)
    simp only [List.drop_zero] at this
    rw [this]
    refine digB_map_congr _ fun t ht => ?_
    have hp := parN_eq_parR X t.1 7 0 (by have := hS t ht; omega)
    simp only [List.drop_zero] at hp
    simp only [tneg, ← hp]
    rfl
  rw [hr1] at hfin
  dsimp only at hfin
  rw [hr, hneg] at hfin
  dsimp only at hfin
  -- the digits and their sums
  set cD : Term → ℕ → ℕ := fun t j => D ^ (N - degM t.1) * cellK (aOf X) t 7 j with hcDdef
  set tD : Term → ℕ := fun t => D ^ (N - degM t.1) * tK (uOf X H) t 7 with htDdef
  have hcD' : ∀ t ∈ S, ∀ j < 8, cD t j < 2 ^ W := fun t ht j hj => by
    have := hcD t ht j hj; simp only [hcDdef]; omega
  have hblk : ∀ t ∈ S, blkF W (cD t) < 2 ^ (8 * W) := fun t ht => blkF_lt W _ (hcD' t ht)
  have hsum : ∀ (q : Term → Bool) (j : ℕ), j < 8 →
      (S.map fun t => if q t then cD t j else 0).sum < 2 ^ W - 1 := by
    intro q j hj
    refine lt_of_le_of_lt ?_ hG
    calc (S.map fun t => if q t then cD t j else 0).sum
        ≤ (S.map fun t => t.2.1 * ((N + 1) * M ^ N)).sum := list_sum_le S _ _ fun t ht => by
          split_ifs
          · exact cellK_le ha hM1 t N _ 7 (hdeg t ht) (hsD t ht) j hj
          · exact Nat.zero_le _
      _ = csum * ((N + 1) * M ^ N) := list_sum_mul S _ _
  have hsumT : (S.map tD).sum < 2 ^ W - 1 := by
    refine lt_of_le_of_lt ?_ hG
    calc (S.map tD).sum ≤ (S.map fun t => t.2.1 * ((N + 1) * M ^ N)).sum :=
          list_sum_le S _ _ fun t ht => tK_le hu hM1 t N _ 7 (hsD t ht)
      _ = csum * ((N + 1) * M ^ N) := list_sum_mul S _ _
  have hsel : ∀ q : Term → Bool, Nat.mod (digB (8 * W) (S.map fun t =>
      if q t then blkF W (cD t) else 0)) (2 ^ (8 * W) - 1) =
      blkF W (fun j => (S.map fun t => if q t then cD t j else 0).sum) := by
    intro q
    have e1 : (S.map fun t => if q t then blkF W (cD t) else 0) =
        S.map fun t => blkF W (fun j => if q t then cD t j else 0) :=
      List.map_congr_left fun t _ => by split_ifs <;> simp [blkF_zero]
    rw [e1, show ∀ x y : ℕ, Nat.mod x y = x % y from fun _ _ => rfl, digB_mod, blkF_sum]
    rw [blkF_sum]
    exact blkF_lt_sub_one W _ (hsum q 0 (by norm_num)) fun j hj => by
      have := hsum q j hj; omega
  have hPn : Nat.land (digB (8 * W) (S.map fun t => blkF W (cD t)))
      (selMask (8 * W) S fun t => tneg sgB t) =
      digB (8 * W) (S.map fun t => if tneg sgB t then blkF W (cD t) else 0) :=
    digB_map_select _ S _ _ hblk
  have hPp : Nat.sub (digB (8 * W) (S.map fun t => blkF W (cD t)))
      (digB (8 * W) (S.map fun t => if tneg sgB t then blkF W (cD t) else 0)) =
      digB (8 * W) (S.map fun t => if !tneg sgB t then blkF W (cD t) else 0) := by
    rw [digB_map_split (8 * W) S (fun t => tneg sgB t) (fun t => blkF W (cD t))]
    rw [show ∀ x y : ℕ, Nat.sub x y = x - y from fun _ _ => rfl, Nat.add_sub_cancel_left]
    exact digB_map_congr _ fun t _ => by cases tneg sgB t <;> rfl
  rw [hPn, hPp, hsel, hsel] at hfin
  set sm : (Term → Bool) → ℕ → ℕ := fun q j => (S.map fun t => if q t then cD t j else 0).sum
    with hsmdef
  have hext : ∀ q : Term → Bool, Nat.land (blkF W (sm q)) (2 ^ W - 1) = sm q 0 := by
    intro q
    rw [show Nat.land (blkF W (sm q)) (2 ^ W - 1) = blkF W (sm q) &&& (2 ^ W - 1) from rfl,
      Nat.and_two_pow_sub_one_eq_mod, blkF_mod W _ (by
        have h0 : sm q 0 < 2 ^ W - 1 := hsum q 0 (by norm_num)
        omega)]
  have hT : Nat.mod (digB W (S.map tD)) (2 ^ W - 1) = (S.map tD).sum := digB_mod W _ hsumT
  have hlinR := linR_spec W (blkF W (sm fun t => !tneg sgB t)) (blkF W (sm fun t => tneg sgB t))
    H 0 0 0
  simp only [zero_add, Nat.mul_one] at hlinR
  have hdgt : ∀ q : Term → Bool, ∀ i < H.length, dgt W (blkF W (sm q)) i = sm q (i + 1) := by
    intro q i hi
    exact blkF_digit W _ (fun j hj => by
      have h0 : sm q j < 2 ^ W - 1 := hsum q j hj
      omega) (i + 1) (by omega)
  rw [hext, hext, hT, hlinR] at hfin
  dsimp only at hfin
  have hlin1 : ∑ i ∈ Finset.range H.length, (H.getD i 0).toNat *
      linT true (dgt W (blkF W (sm fun t => !tneg sgB t)) i) (dgt W (blkF W (sm fun t => tneg sgB t)) i) =
      ∑ i ∈ Finset.range H.length, (H.getD i 0).toNat *
      linT true (sm (fun t => !tneg sgB t) (i + 1)) (sm (fun t => tneg sgB t) (i + 1)) :=
    Finset.sum_congr rfl fun i hi => by
      rw [hdgt _ i (Finset.mem_range.mp hi), hdgt _ i (Finset.mem_range.mp hi)]
  have hL1 : ∑ i ∈ Finset.range H.length, (H.getD i 0).toNat *
      (dgt W (blkF W (sm fun t => !tneg sgB t)) i + dgt W (blkF W (sm fun t => tneg sgB t)) i) =
      ∑ i ∈ Finset.range H.length, (H.getD i 0).toNat *
      (sm (fun t => !tneg sgB t) (i + 1) + sm (fun t => tneg sgB t) (i + 1)) :=
    Finset.sum_congr rfl fun i hi => by
      rw [hdgt _ i (Finset.mem_range.mp hi), hdgt _ i (Finset.mem_range.mp hi)]
  rw [hlin1, hL1] at hfin
  simp only [Nat.add_eq] at hfin
  -- the closed forms
  set ax := X.map Int.natAbs with haxdef
  set Hn := H.map Int.toNat with hHndef
  have hax : ax.length ≤ 7 := by simp [ax, hX]
  have hHn : Hn.length ≤ 7 := by simp [Hn]; omega
  have hmono : ∀ t ∈ S, monoNat ax t.1 = prK (aOf X) t.1 7 := by
    intro t ht
    have := monoNat_prod ax t.1 0 7 (hS t ht)
    simp only [List.drop_zero, zero_add] at this
    rw [this, prK]
    exact Finset.prod_congr rfl fun i _ => by rw [haxdef, getD_map_natAbs]
  have E1 : ∀ t ∈ S, cD t 0 = tc D N t * monoNat ax t.1 := by
    intro t ht
    simp only [hcDdef, cellK_zero, tc, hmono t ht]
    ring
  have hgd : ∀ i, ax.getD i 0 = aOf X i := fun i => getD_map_natAbs X i
  have E2 : ∀ t ∈ S, ∀ j < 7, cD t (j + 1) = tc D N t * derivN ax j 0 t.1 := by
    intro t ht j hj
    have := derivN_prod ax j t.1 0 7 (hS t ht)
    simp only [zero_add, Nat.zero_le, ite_true, Nat.sub_zero, hgd] at this
    simp only [hcDdef, cellK_succ, hj, ite_true, tc, this, dprK]
    ring
  have E3 : ∀ t ∈ S, tD t = tc D N t * monoNat (addL7 ax Hn) t.1 := by
    intro t ht
    have hgu : ∀ i, (addL7 ax Hn).getD i 0 = uOf X H i := fun i => by
      rw [getD_addL7 ax Hn hax hHn, haxdef, hHndef, getD_map_natAbs, getD_map_toNat]; rfl
    have := monoNat_prod (addL7 ax Hn) t.1 0 7 (hS t ht)
    simp only [List.drop_zero, zero_add, hgu] at this
    simp only [htDdef, tK_eq, tc, this, prK]
    ring
  have hsplit : ∀ f : Term → ℕ, (S.map f).sum =
      (S.map fun t => if !tneg sgB t then f t else 0).sum +
        (S.map fun t => if tneg sgB t then f t else 0).sum := by
    intro f
    induction S with
    | nil => simp
    | cons t S ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        cases tneg sgB t <;> simp <;> ring
  -- the slot sums, over all seven variables
  have hzero : ∀ j, H.length ≤ j → (H.getD j 0).toNat = 0 := fun j hj => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]
  have hdP : ∀ j < 7, (S.map fun t => if tneg sgB t then 0 else tc D N t * derivN ax j 0 t.1).sum =
      sm (fun t => !tneg sgB t) (j + 1) := fun j hj => by
    simp only [hsmdef]
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    rw [E2 t ht j hj]
    by_cases hq : tneg sgB t = true <;> simp [hq]
  have hdN : ∀ j < 7, (S.map fun t => if tneg sgB t then tc D N t * derivN ax j 0 t.1 else 0).sum =
      sm (fun t => tneg sgB t) (j + 1) := fun j hj => by
    simp only [hsmdef]
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    rw [E2 t ht j hj]
  have hlinS : ∑ j ∈ Finset.range 7, linT true (pSlot D N ax sgB Hn S true j)
      (pSlot D N ax sgB Hn S false j) = ∑ i ∈ Finset.range H.length, (H.getD i 0).toNat *
        linT true (sm (fun t => !tneg sgB t) (i + 1)) (sm (fun t => tneg sgB t) (i + 1)) := by
    rw [Finset.sum_congr rfl fun j hj => by
      rw [(pSlot_pair D N ax sgB Hn S j).1, hdP j (Finset.mem_range.mp hj),
        hdN j (Finset.mem_range.mp hj), hHndef, getD_map_toNat]]
    exact (Finset.sum_subset (Finset.range_subset_range.mpr (by omega : H.length ≤ 7))
      (fun j _ hj => by rw [Finset.mem_range, not_lt] at hj; rw [hzero j hj, zero_mul])).symm
  have hLS : ∑ j ∈ Finset.range 7, (pSlot D N ax sgB Hn S true j +
      pSlot D N ax sgB Hn S false j) = ∑ i ∈ Finset.range H.length, (H.getD i 0).toNat *
        (sm (fun t => !tneg sgB t) (i + 1) + sm (fun t => tneg sgB t) (i + 1)) := by
    rw [Finset.sum_congr rfl fun j hj => by
      rw [(pSlot_pair D N ax sgB Hn S j).2, hdP j (Finset.mem_range.mp hj),
        hdN j (Finset.mem_range.mp hj), hHndef, getD_map_toNat]]
    exact (Finset.sum_subset (Finset.range_subset_range.mpr (by omega : H.length ≤ 7))
      (fun j _ hj => by rw [Finset.mem_range, not_lt] at hj; rw [hzero j hj, zero_mul])).symm
  refine cheapI_of_slots S D ax sgB Hn true hD hS hax hHn ?_
  have hA : (S.map fun t => if tneg sgB t then tc D N t * monoNat ax t.1 else 0).sum =
      sm (fun t => tneg sgB t) 0 := by
    simp only [hsmdef]
    exact congrArg List.sum (List.map_congr_left fun t ht => by rw [E1 t ht])
  have hB : (S.map fun t => if tneg sgB t then 0 else tc D N t * monoNat ax t.1).sum =
      sm (fun t => !tneg sgB t) 0 := by
    simp only [hsmdef]
    exact congrArg List.sum (List.map_congr_left fun t ht => by
      rw [E1 t ht]
      by_cases hq : tneg sgB t = true <;> simp [hq])
  have hV : (S.map fun t => tc D N t * monoNat ax t.1).sum =
      sm (fun t => !tneg sgB t) 0 + sm (fun t => tneg sgB t) 0 := by
    rw [hsplit, hsmdef]
    congr 1
    all_goals exact congrArg List.sum (List.map_congr_left fun t ht => by rw [E1 t ht])
  have hTT : (S.map fun t => tc D N t * monoNat (addL7 ax Hn) t.1).sum = (S.map tD).sum :=
    congrArg List.sum (List.map_congr_left fun t ht => (E3 t ht).symm)
  rw [hA, hB, hV, hTT, hlinS, hLS]
  exact le_trans (le_of_eq (by rfl)) (le_trans hfin (le_of_eq (by ring)))

end Noperts.Triakis.CornerKernel
