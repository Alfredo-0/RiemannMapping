import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

example (P : Prop) : P → P := by
  intro h
  exact h

section
variable (a : ℝ)
variable (h : 0 ≤ a )
theorem lemma1 : ∀x : ℝ, 0≤x → |x|=x := sorry

#check lemma1
#check lemma1 a
#check lemma1 a h
end


theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε ε_pos ε_le_one x_lt_ε y_lt_ε
  calc
    |x * y| = |x| * |y| := by rw [abs_mul]
    _ ≤ |x| * ε := by
      apply mul_le_mul
      exact le_refl _
      exact le_of_lt y_lt_ε
      exact abs_nonneg _
      exact abs_nonneg _
    _ < 1 * ε := by
      apply mul_lt_mul_of_pos_of_nonneg'
      exact lt_of_lt_of_le x_lt_ε ε_le_one
      exact le_refl _
      exact ε_pos
      exact zero_le_one' ℝ
    _ = ε := by rw [one_mul]

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

open Function

example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b := @h

example {f g : ℝ → ℝ} (mf : Monotone f) (mg : Monotone g) :
  Monotone (fun x ↦ f x + g x) := by
  intro a b hab
  apply add_le_add
  exact mf hab
  exact mg hab

example {f g : ℝ → ℝ} (mf : Monotone f) (mg : Monotone g) :
  Monotone (fun x ↦ f x + g x) :=
  fun a b hab ↦ add_le_add (mf hab) (mg hab)

example {f : ℝ → ℝ} {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) :
  Monotone fun x ↦ c * f x := by
  intro a b hab
  dsimp
  apply mul_le_mul_of_nonneg_left
  apply (mf hab)
  apply nnc

example {f : ℝ → ℝ} {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) :
  Monotone fun x ↦ c * f x :=
  fun a b hab ↦ mul_le_mul_of_nonneg_left (mf hab) nnc

example {f g : ℝ → ℝ} (mf : Monotone f) (mg : Monotone g) :
  Monotone fun x ↦ f (g x) := by
  intro a b hab
  dsimp
  apply mf
  apply (mg hab)

example {f g : ℝ → ℝ} (mf : Monotone f) (mg : Monotone g) :
  Monotone fun x ↦ f (g x) :=
  fun a b hab ↦ mf (mg hab)

example (c : ℝ) : Injective fun x ↦ x + c := by
intro x1 x2 h'
exact (add_left_inj c).mp h'

example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c*x := by
  intro x1 x2 h'
  exact (mul_right_inj' h).mp  h'
