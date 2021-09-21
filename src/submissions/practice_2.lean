/-
Wyndham White (working alone)
wrw2ztk
https://github.com/wyndhamv/cs2120f21.git
-/

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

      --q case
        assume q,
        have paq : P ∧ Q := and.intro p q,
        apply or.intro_left,
        exact paq, 
     
      --r case
        assume r,
        have par : P ∧ R := and.intro p r,
        apply or.intro_right,
        exact par,

     
    --backwards
      assume paqopar,
      apply or.elim paqopar,

        --paq
          assume paq,
          apply and.intro _,
          have q : Q := and.elim_right paq,
          apply or.intro_left R q,

          have p : P := and.elim_left paq,
          exact p,

        --par
          assume par,
          have p : P := and.elim_left par,
          have r : R := and.elim_right par,
          apply and.intro,
          exact p,
          apply or.intro_right Q r,

end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,

    --forwards
      assume poqar,
      apply and.intro,
      apply or.elim poqar,
        --p
          assume p,
          apply or.intro_left Q p,
        --qar
          assume qar,
          have q : Q := and.elim_left qar,
          apply or.intro_right P q,
        --por
          apply or.elim poqar,
            --p
              assume p,
              apply or.intro_left R p,
            --qar
              assume qar,
              have r : R := and.elim_right qar,
              apply or.intro_right P r,

    --backwards
      assume poqapor,
      have poq : (P∨Q) := and.elim_left poqapor,
      have por : (P∨R) := and.elim_right poqapor,
      apply or.elim poq,
        --poq elim
          --assume p
            assume p,
            apply or.intro_left (Q∧R) p,
          --assume q
            assume q,
            apply or.elim por,
              --assume p
                assume p,
                apply or.intro_left (Q∧R) p,
              --assume r
                assume r,
                have qar : (Q∧R) := and.intro q r,
                apply or.intro_right P qar,
      
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,

  --f
    assume papoq,
    have p : P := and.elim_left papoq,
    exact p,

  --b
    assume p,
    apply and.intro _,
    apply or.intro_left Q p,
    exact p,

end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
    --f
      assume popaq,
      apply or.elim popaq,
        assume p,
        exact p,

        assume paq,
        have p : P := and.elim_left paq,
        exact p,
    --b
      assume p,
      apply or.intro_left _ _,
      exact p,
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro _ _,

  assume pot,
  exact true.intro,

  assume t,
  apply or.intro_right P t,
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro,

  assume pof,
  apply or.elim pof,
  assume p,
  exact p,

  assume f,
  cases f,
  
  assume P,
  apply or.intro_left false P,
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
    assume P,
    apply iff.intro,

    assume pat,
    apply and.elim_left pat,

    assume p,
    apply and.intro,
    exact p,
    exact true.intro,
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro,

  assume paf,
  have f : false := and.elim_right paf,
  exact f,

  assume f,
  cases f,
end


