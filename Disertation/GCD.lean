import Disertation.Basic
import Mathlib

def euclid (a b : ℕ) :=
    if h : b = 0 then  a
    else euclid b (a % b)
    termination_by b
    decreasing_by
        apply Nat.mod_lt
        (expose_names; exact Nat.zero_lt_of_ne_zero h)

        -- induction b
        -- contradiction

-- def ex_euclid' (a b c b : ℕ) :=
--     a

-- def ex_euclid (a b : ℕ) :=
--     ex_euclid' a b 0 0



#eval euclid 324 541



theorem euclid_a_zero : euclid a 0 = a :=
    by
    sorry




theorem DivA : euclid a b ∣ a ∧ euclid a b ∣ b  :=
    by
    induction b using Nat.strong_induction_on generalizing a with
    | h b ih =>
    by_cases hb : b = 0
    rw [hb]
    simp
    unfold euclid
    simp
    -- have EB : euclid a b ∣ b
    -- unfold euclid
    -- simp
    -- rw [ite_eq_right hb]
    -- have ba: a % b < b
    -- apply Nat.mod_lt
    -- exact Nat.zero_lt_of_ne_zero hb


    -- sorry
    have EB : euclid a b ∣ b
    unfold euclid
    simp
    rw [ite_eq_right hb]
    have hba: a % b < b
    apply Nat.mod_lt
    exact Nat.zero_lt_of_ne_zero hb
    have h := @ih (a % b ) hba b
    exact h.left
    -- rw [ih] at hba
    have EA : euclid a b ∣ a

    -- unfold euclid
    -- simp
    -- rw [ite_eq_right hb]
    have ba: a % b < b
    apply Nat.mod_lt
    exact Nat.zero_lt_of_ne_zero hb
    have habab : euclid a b ∣ (a % b)
    unfold euclid
    simp
    rw [ite_eq_right hb]
    have h:= @ih (a % b) ba b; exact h.right
    exact (Nat.dvd_mod_iff EB).mp habab
    exact ⟨ EA,EB⟩


-- theorem comEuclid : euclid a b = euclid b a :=
--     by
--     induction b using Nat.strong_induction_on generalizing a with
--     | h b ih =>
--     by_cases hb : b = 0
--     rw [hb]
--     unfold euclid
--     simp
