module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Naturals as digit vectors

`digB B [x₀, x₁, …] = x₀ + 2^B x₁ + 2^(2B) x₂ + …`.  With digits below `2^B`, bitwise
`&&&` and `^^^` act digitwise, sums and scalar multiples are digitwise without any bound,
and `% (2^B - 1)` sums the digits.  The packed checkers use this to evaluate one operation
on many small numbers at once (one GMP operation in the kernel).
-/

namespace Noperts.Triakis.PackedDigits

/-- `x₀ + 2^B x₁ + 2^(2B) x₂ + …`. -/
def digB (B : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + 2 ^ B * digB B xs

@[simp] theorem digB_nil (B : ℕ) : digB B [] = 0 := rfl

theorem digB_cons (B x : ℕ) (xs : List ℕ) : digB B (x :: xs) = x + 2 ^ B * digB B xs := rfl

section
variable {α : Type*} (B : ℕ)

theorem digB_map_add (L : List α) (f g : α → ℕ) :
    digB B (L.map f) + digB B (L.map g) = digB B (L.map fun t => f t + g t) := by
  induction L with
  | nil => rfl
  | cons t L ih =>
      simp only [List.map_cons, digB_cons, ← ih]
      ring

theorem digB_map_mul (c : ℕ) (L : List α) (f : α → ℕ) :
    c * digB B (L.map f) = digB B (L.map fun t => c * f t) := by
  induction L with
  | nil => simp
  | cons t L ih =>
      simp only [List.map_cons, digB_cons, ← ih]
      ring

theorem digB_map_zero (L : List α) : digB B (L.map fun _ => 0) = 0 := by
  induction L with
  | nil => rfl
  | cons t L ih => simp only [List.map_cons, digB_cons, ih]; simp

theorem digB_map_congr {L : List α} {f g : α → ℕ} (h : ∀ t ∈ L, f t = g t) :
    digB B (L.map f) = digB B (L.map g) := by
  rw [List.map_congr_left h]

/-- The selected and the other digits add up. -/
theorem digB_map_split (L : List α) (p : α → Bool) (f : α → ℕ) :
    digB B (L.map f) = digB B (L.map fun t => if p t then f t else 0) +
      digB B (L.map fun t => if p t then 0 else f t) := by
  rw [digB_map_add]
  exact digB_map_congr B fun t _ => by cases p t <;> simp

theorem combine_and (x m X M : ℕ) (hx : x < 2 ^ B) (hm : m < 2 ^ B) :
    (x + 2 ^ B * X) &&& (m + 2 ^ B * M) = (x &&& m) + 2 ^ B * (X &&& M) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.add_comm x, Nat.add_comm m, Nat.add_comm (x &&& m), Nat.testBit_and,
    Nat.testBit_two_pow_mul_add _ hx, Nat.testBit_two_pow_mul_add _ hm,
    Nat.testBit_two_pow_mul_add _ (Nat.and_lt_two_pow _ hm), Nat.testBit_and, Nat.testBit_and]
  split_ifs <;> rfl

theorem combine_xor (x m X M : ℕ) (hx : x < 2 ^ B) (hm : m < 2 ^ B) :
    (x + 2 ^ B * X) ^^^ (m + 2 ^ B * M) = (x ^^^ m) + 2 ^ B * (X ^^^ M) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.add_comm x, Nat.add_comm m, Nat.add_comm (x ^^^ m), Nat.testBit_xor,
    Nat.testBit_two_pow_mul_add _ hx, Nat.testBit_two_pow_mul_add _ hm,
    Nat.testBit_two_pow_mul_add _ (Nat.xor_lt_two_pow hx hm), Nat.testBit_xor, Nat.testBit_xor]
  split_ifs <;> rfl

theorem digB_map_and (L : List α) (f g : α → ℕ) (hf : ∀ t ∈ L, f t < 2 ^ B)
    (hg : ∀ t ∈ L, g t < 2 ^ B) :
    digB B (L.map f) &&& digB B (L.map g) = digB B (L.map fun t => f t &&& g t) := by
  induction L with
  | nil => simp
  | cons t L ih =>
      simp only [List.map_cons, digB_cons]
      rw [combine_and B _ _ _ _ (hf t List.mem_cons_self) (hg t List.mem_cons_self),
        ih (fun u hu => hf u (List.mem_cons_of_mem _ hu)) (fun u hu => hg u (List.mem_cons_of_mem _ hu))]

theorem digB_map_xor (L : List α) (f g : α → ℕ) (hf : ∀ t ∈ L, f t < 2 ^ B)
    (hg : ∀ t ∈ L, g t < 2 ^ B) :
    digB B (L.map f) ^^^ digB B (L.map g) = digB B (L.map fun t => f t ^^^ g t) := by
  induction L with
  | nil => simp
  | cons t L ih =>
      simp only [List.map_cons, digB_cons]
      rw [combine_xor B _ _ _ _ (hf t List.mem_cons_self) (hg t List.mem_cons_self),
        ih (fun u hu => hf u (List.mem_cons_of_mem _ hu)) (fun u hu => hg u (List.mem_cons_of_mem _ hu))]

/-- Selecting digits by a mask of all-ones and zero digits. -/
theorem digB_map_select (L : List α) (f : α → ℕ) (p : α → Bool) (hf : ∀ t ∈ L, f t < 2 ^ B) :
    digB B (L.map f) &&& digB B (L.map fun t => if p t then 2 ^ B - 1 else 0) =
      digB B (L.map fun t => if p t then f t else 0) := by
  rw [digB_map_and B L f _ hf (fun t _ => by have := Nat.two_pow_pos B; split_ifs <;> omega)]
  refine digB_map_congr B fun t ht => ?_
  split_ifs
  · rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hf t ht)]
  · exact Nat.and_zero _

theorem digB_lt (L : List α) (f : α → ℕ) (hf : ∀ t ∈ L, f t < 2 ^ B) :
    digB B (L.map f) < 2 ^ (B * L.length) := by
  induction L with
  | nil => simp
  | cons t L ih =>
      simp only [List.map_cons, digB_cons, List.length_cons]
      have h1 := hf t List.mem_cons_self
      have h2 := ih fun u hu => hf u (List.mem_cons_of_mem _ hu)
      calc f t + 2 ^ B * digB B (L.map f) < 2 ^ B + 2 ^ B * digB B (L.map f) := by omega
        _ = 2 ^ B * (digB B (L.map f) + 1) := by ring
        _ ≤ 2 ^ B * 2 ^ (B * L.length) := Nat.mul_le_mul_left _ h2
        _ = 2 ^ (B * (L.length + 1)) := by rw [← pow_add]; ring_nf

/-- The digit sum, modulo `2^B - 1`. -/
theorem digB_modEq_sum (L : List ℕ) : digB B L ≡ L.sum [MOD 2 ^ B - 1] := by
  have h1 : 2 ^ B ≡ 1 [MOD 2 ^ B - 1] := by
    have := Nat.one_le_two_pow (n := B)
    exact (Nat.modEq_iff_dvd' this).mpr dvd_rfl |>.symm
  induction L with
  | nil => rfl
  | cons x L ih =>
      simp only [digB_cons, List.sum_cons]
      have := Nat.ModEq.mul h1 ih
      rw [one_mul] at this
      exact Nat.ModEq.add_left x this

theorem digB_mod (L : List ℕ) (h : L.sum < 2 ^ B - 1) : digB B L % (2 ^ B - 1) = L.sum := by
  rw [digB_modEq_sum B L, Nat.mod_eq_of_lt h]

/-- Digit `j` of a digit vector. -/
theorem digB_digit (L : List ℕ) (hL : ∀ x ∈ L, x < 2 ^ B) (j : ℕ) :
    (digB B L >>> (B * j)) &&& (2 ^ B - 1) = L.getD j 0 := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  induction L generalizing j with
  | nil => simp
  | cons x L ih =>
      have hx := hL x List.mem_cons_self
      cases j with
      | zero => simp [digB_cons, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
      | succ j =>
          rw [digB_cons, show B * (j + 1) = B + B * j by ring, pow_add, ← Nat.div_div_eq_div_mul,
            Nat.add_mul_div_left _ _ (Nat.two_pow_pos B), Nat.div_eq_of_lt hx, zero_add,
            ih (fun u hu => hL u (List.mem_cons_of_mem _ hu))]
          simp

end

end Noperts.Triakis.PackedDigits
