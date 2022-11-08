import Sets.Basic
import Functions.Basic
import Relations.Basic

open Set
open Func
open Relations 

variable { α : Type }

-- Problem 1 

theorem subset_refl : Reflexive (@Subset α) := sorry 

theorem subset_antisymm : AntiSymmetric (@Subset α) := sorry  

theorem subset_trans : Transitive (@Subset α) := sorry 

-- Problem 2 

def Rel (f : α → α) (a₁ a₂ : α) : Prop := sorry 

theorem refl_id (f : α → α) (h : Reflexive (Rel f) ) : f = id := sorry  

theorem symm_involution (f : α → α) (h : Symmetric (Rel f)) : f ∘ f = id := sorry  

theorem trans_idempotent (f : α → α) (h : Transitive (Rel f)) : f ∘ f = f := sorry  
