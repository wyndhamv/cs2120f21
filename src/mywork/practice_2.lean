/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

example : false := _    -- trick question? why?
-- False is the uninhabited propositional type in lean
-- i.e. there is no proof of it

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin

  assume P,
  apply iff.intro _ _,
  --forwards
    assume porp,
    apply or.elim porp,
    --or case 1
    assume p,
    exact p,
    --or case 2
    assume p,
    exact p,
  --backwards
    assume p,
    apply or.intro_left _ _,
    exact p,

end

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin

  assume P,
  apply iff.intro _ _,
  --forwards
    assume pap,
    apply and.elim_left pap,
  --backwards
    assume p,
    apply and.intro p p,

end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin

  assume P Q,
  apply iff.intro _ _,
  --forwards
    assume paq,
    apply or.elim paq,
      --or case 1
      assume p,
      apply or.intro_right Q p,
      --or case 2
      assume q,
      apply or.intro_left P q,
  --backwards
    assume qop,
    apply or.elim qop,
      --or case 1
        assume q,
        apply or.intro_right P q,
      --or case 2
        assume p,
        apply or.intro_left Q p,

end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
    assume P Q,
    apply iff.intro _ _,
    --forwards
      assume paq,
      apply and.intro _ _,
      apply and.elim_right paq,
      apply and.elim_left paq,
    --backwards
      assume qap,
      apply and.intro _ _,
      apply and.elim_right qap,
      apply and.elim_left qap,

end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
    --forwards
     assume paqor,
     have p : P := and.elim_left paqor,
     have qor : Q ∨ R := and.elim_right paqor,
     apply or.elim qor,

     assume q,
     have paq : P ∧ Q := and.intro p q,
     
     --apply or.intro_left paq (P ∧ R),
     
    --backwards

end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
end


