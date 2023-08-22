example (p q r : Prop) : ((p ∨ q) → r) ↔ ((p → r) ∧ (q → r)) :=
begin
  split,
  { 
    intro h,
    split,
    {
      intro hp,
      apply h,
      left,
      assumption,
    },
    { 
      intro hp,
      apply h,
      right,
      assumption,
    } 
  },
  {  
    intro h,
    cases h with pr qr,
    intro hp,
    cases hp with p q,
    {
      apply pr,
      assumption,
    },
    { 
      apply qr,
      assumption,
    }
  },
end