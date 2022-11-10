-- Take these. They might be useful on your journey. 

theorem Nat.succ_of_gt {n : Nat} (h : ∃ m, m < n) : ∃ k, n = k + 1 := by 
  have : n ≠ 0 := by 
    intro h' 
    have ⟨m,h⟩ := h 
    rw [h'] at h 
    exact Nat.not_lt_zero m h
  have : _ := Eq.symm (Nat.succ_pred this)
  exists pred n 

theorem Nat.lt_add_cancel_right {n m l : Nat} (h : n + l < m + l) : n < m := by 
  match l with 
  | 0 => simp at h; assumption 
  | j+1 => 
    repeat (rw [←Nat.add_assoc] at h)
    have : n + j < m + j := by 
      have : _ := Nat.pred_le_pred (Nat.le_of_lt h) 
      repeat (rw [←Nat.succ_eq_add_one,Nat.pred_succ] at this)
      have : _ := Nat.lt_of_le_of_ne this 
      have ne : n+j ≠ m+j := by 
        intro h' 
        rw [h'] at h 
        exact Nat.ne_of_lt h (by rfl) 
      exact this ne 
    exact Nat.lt_add_cancel_right this 

theorem Nat.lt_succ_of_lt {n m : Nat} (h : n < m) : n < m + 1 := by 
  have this : n + 1 < m + 1 := Nat.succ_lt_succ h 
  have that : n < n +1 := Nat.lt_succ_self n 
  exact Nat.lt_trans that this 

-- Fill in the sorries for the following to correctly define binomial 
-- coefficients recursively and prove Binom n k = 0 for n < k. 

def Binom (n k : Nat) : Nat := 
  match n, k with 
  | _, 0 => sorry 
  | 0, _+1 => sorry  
  | n+1, k+1 => sorry 

theorem fst_lt_snd_binom_zero (n k : Nat) (h : n < k) : Binom n k = 0 := sorry 
