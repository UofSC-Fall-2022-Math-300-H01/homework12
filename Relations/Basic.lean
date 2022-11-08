-- import Ints.Lemmas
import Sets.Basic

section Eg

variable (n m : Nat) 

#check n < m 

end Eg 

-- What are the natural numbers in Lean? How do we prove things about them? We 
-- will come back to these 
namespace Nat

theorem mul_nonzero_cancel {a b c : Nat} (h : a ≠ 0) (h' : a*b = a*c) : b = c := sorry 

theorem prod_eq_one { a b : Nat } (h : a*b = 1) : a = 1 ∧ b = 1 := sorry

end Nat 

namespace Relations 

variable { α : Type } 

def Reflexive (R : α → α → Prop) : Prop := ∀ x, R x x 

def Irreflexive (R : α → α → Prop) : Prop := ∀ x, ¬ R x x 

def Symmetric (R : α → α → Prop) : Prop := ∀ ⦃x y⦄, R x y → R y x 

def Asymmetric (R : α → α → Prop) : Prop := ∀ ⦃x y⦄, R x y → ¬ R y x

def AntiSymmetric (R : α → α → Prop) : Prop := ∀ ⦃x y⦄, R x y → R y x → x = y 

def Total (R : α → α → Prop) : Prop := ∀ x y, R x y ∨ R y x 

def Transitive (R : α → α → Prop) : Prop := ∀ ⦃x y z⦄, R x y → R y z → R x z 

class Equiv (R : α → α → Prop) where 
  refl : Reflexive R
  symm : Symmetric R
  trans : Transitive R 

instance : Equiv (@Eq α) where 
  refl := Eq.refl
  symm := @Eq.symm α 
  trans := @Eq.trans α 

class PartialOrder (R : α → α → Prop) where
  refl : Reflexive R 
  antisymm : AntiSymmetric R 
  trans : Transitive R 

class TotalOrder (R : α → α → Prop) where 
  antisymm : AntiSymmetric R 
  total : Total R 

theorem refl_not_irrefl { R : α → α → Prop } (a : α) (h : Reflexive R) : ¬ Irreflexive R := 
  fun h' => h' a (h a) 

theorem irrefl_not_refl { R : α → α → Prop } (a : α) (h : Irreflexive R) : ¬ Reflexive R := 
  fun h' => h a (h' a) 

-- theorem eq_or {P : Prop} (h : P ∨ P) : P := by cases h; repeat assumption 

theorem total_refl { R : α → α → Prop } (h : Total R) : Reflexive R := fun a => eq_or (h a a) where 
  eq_or {P : Prop} (h : P ∨ P) : P := by cases h; repeat assumption 

def Divides (a b : Nat) : Prop := ∃ c, b = c*a 
infix:60 " | " => Divides

theorem div_refl : Reflexive Divides := by
  intro a 
  have : a = 1*a := Eq.symm (Nat.one_mul a)
  exists 1

theorem div_not_irrefl : ¬ Irreflexive Divides := refl_not_irrefl 0 div_refl 

theorem div_antisym : AntiSymmetric Divides := by
  intro a b h₁ h₂ 
  have ⟨c₁,h₁⟩ := h₁ 
  have ⟨c₂,h₂⟩ := h₂ 
  by_cases h : a = 0
  · rw [h,Nat.mul_zero,←h] at h₁ 
    exact Eq.symm h₁ 
  · rw [h₁,←Nat.mul_assoc,Nat.mul_comm] at h₂ 
    conv at h₂ => lhs ; rw [←Nat.mul_one a] 
    have : 1 = c₂ * c₁ := Nat.mul_nonzero_cancel h h₂
    have : c₁ = 1 := (Nat.prod_eq_one (Eq.symm this)).right 
    rw [this,Nat.one_mul a] at h₁ 
    exact Eq.symm h₁ 

theorem div_trans : Transitive Divides := by 
  intro a b c h₁ h₂ 
  have ⟨d₁,h₁⟩ := h₁ 
  have ⟨d₂,h₂⟩ := h₂ 
  rw [h₁,←Nat.mul_assoc] at h₂ 
  exists d₂*d₁ 

instance : PartialOrder Divides where 
  refl := div_refl 
  antisymm := div_antisym
  trans := div_trans 

end Relations 
