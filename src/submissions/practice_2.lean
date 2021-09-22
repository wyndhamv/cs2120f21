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
--Proof: True is proven true by using its one proof, true.intro

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
/-
Proof:
Assume that P is a proposition.
We must prove P ∨ P implies P. To do this, we split into case analysis where
we prove that P implies P (first case) and that P implies P (second case). Both
can be proven by assuming a proof of p and then applying the proof.
Then, we must prove that P implies P ∨ P. We assume a proof of P, then apply the
intro rule for or to leave the goal as P. Then, we can apply the proof of
P to prove P.
QED.
-/


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
/-
Proof:
Assume that P is a proposition.
We must prove that P ∧ P implies P. To do this, we assume a proof of
P ∧ P. Then, we can use the elimination rule (left variation) of ∧ to 
get a proof of P, which is then applied.
Then, we must prove that P implies P ∧ P. To do this, we assume a proof
of P. Then, we can construct a proof of P ∧ P using the introduction rule
for and to combine a proof of P with a proof of P.
QED.
-/

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
/-
Proof:
Assume that P and Q are propositions.
First we must prove that P ∨ Q implies Q ∨ P. To do this, we assume 
P ∨ Q. Then, we go into case analysis. In the case where P is true, 
we apply the introduction rule for ∨ with the proof of P to prove
Q ∨ P. In the case where Q is true, we apply the intro rule for ∨ with
the proof of Q to prove Q ∨ P.
Then, we must prove that Q ∨ P implies P ∨ Q. To do this, we assume 
Q ∨ P. Then, we go into case analysis. In the case where Q is true, 
we apply the introduction rule for ∨ with the proof of Q to prove
Q ∨ P. In the case where P is true, we apply the intro rule for ∨ with
the proof of P to prove Q ∨ P.
QED.
-/

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
/-
Proof:
Assume that P and Q are propositions.
First we must prove that P ∧ Q implies Q ∧ P. We assume a proof of 
P ∧ Q (paq), then split the final goal into proving P and proving Q individually using the elimination rule for ∧.
We prove P by applying the elimination rule for ∧ to the 
right side of paq, then we prove Q by applying the elimination rule
for ∧ to the left side of paq.
Then, we must prove that Q ∧ P implies P ∧ Q. We assume a proof of 
Q ∧ P (qap), then split the final goal into proving Q and proving P individually using the elimination rule for ∧.
We prove P by applying the elimination rule for ∧ to the 
right side of qap, then we prove Q by applying the elimination rule
for ∧ to the left side of qap.
QED.
-/


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
/-
Proof:
Assume that P, Q, and R are propositions.
First we must prove that P ∧ (Q ∨ R) implies (P ∧ Q) ∨ (P ∧ R). Assume a proof of
P ∧ (Q ∨ R), then use the elimination rule for ∧ to split it into a proof of P and a 
proof of Q ∨ R. Then, use case analysis by applying the elimination rule for or to the proof
of Q ∨ R. In the case where Q is true, assume a proof of it. Then, use it with the proof of P
to construct a proof of P ∧ Q through the introduction rule of and. Apply the proof of P ∧ Q.
In the case whee R is true assume a proof of it. Then, use it with the proof of P
to construct a proof of P ∧ R through the introduction rule of and. Apply the proof of P ∧ R.

Then, we must prove that (P ∧ Q) ∨ (P ∧ R) implies P ∧ (Q ∨ R). Assume a proof of 
(P ∧ Q) ∨ (P ∧ R). Then, use case analysis to prove the implication using either possibility
of the or. For the P ∧ Q case, assume a proof of P ∧ Q. Then split the final goal into proving P and
proving Q ∨ R by applying the intro rule for ∧. Construct a proof of Q by using the elimination rule
for ∧ on the proof of P ∧ Q, then apply the intro rule for or to prove Q ∨ R. To prove P, construct
a proof of P using the elimination rule for ∧ on the proof of P ∧ Q. Then, apply the proof of P.

For the P ∧ R case, assume a proof of P ∧ R. Then split the final goal into proving P and
proving Q ∨ R by applying the intro rule for ∧. Construct a proof of R by using the elimination rule
for ∧ on the proof of P ∧ R, then apply the intro rule for or to prove Q ∨ R. To prove P, construct
a proof of P using the elimination rule for ∧ on the proof of P ∧ Q. Then, apply the proof. 
QED.

-/

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
/-
Proof:
Assume P, Q, and R are propositions.
First we must prove that P ∨ (Q ∧ R) implies (P ∨ Q) ∧ (P ∨ R). Assume a proof of
(P ∨ Q) ∧ (P ∨ R) (poqar). Then, split the final goal into proving P ∨ Q and P ∨ R
individually. Then, go into case analysis by applying the elimination rule for or to poqar. 
For the case where P is true, assume a proof of P. Then, use the introduction rule for or
to prove P ∨ Q using the proof of P. 
For the case of Q ∧ R, assume a proof of it (qar). Then, construct a proof of Q by applying the
elimination rule for and to qar. Prove P ∨ Q by applying the introduction rule for or
-/

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
/-
Proof:
Assume P and Q are propositions. 
First we must prove that P ∧ (P ∨ Q) implies P. Assume a proof of P ∧ (P ∨ Q), then
construct a proof of P by applying the elimination rule for ∧ to the proof of P ∧ (P ∨ Q). 
Apply the proof of P. 
Then, we must prove that P implies P ∧ (P ∨ Q). Assume a proof of P. 
Apply the introduction rule for ∧ to split the final goal into proving P and 
proving P ∨ Q. Prove P by applying the proof of P. Prove P ∨ Q by applying the introduction rule
for ∨ with the proof of P and the proposition Q.
QED.
-/

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
/-
Proof: 
Assume P and Q are propositions. 
First we must prove that P ∨ (P ∧ Q) implies P. Assume a proof of 
P ∨ (P ∧ Q), then go into case analysis by applying the elimination rule for or to that proof. 
In the case where P implies P, assume a proof of P and then apply it. 
In the case where P ∧ Q implies P, assume a proof of P ∧ Q. Then, construct a 
proof of P by applying the elimination rule for and to the proof of P ∧ Q. Then,
apply the proof of P. 
Then, we must prove that P implies P ∨ (P ∧ Q). To do this, limit the goal to just P implies P
by applying the introduction rule for ∨. Then, assume P. Then, apply P.
QED.
-/

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro _ _,

  assume pot,
  exact true.intro,

  assume t,
  apply or.intro_right P t,
end
/-
Proof:
Assume P is a proposition.
First we must prove that P ∨ true implies true. Assume a proof
of P ∨ true, then apply true.intro to prove true.
Then, we must prove P ∨ true given true. Assume a proof of true,
then apply it with the introduction rule for ∨ to construct a proof of
P ∨ true. 
QED.  
-/

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
/-
Proof:
Assume P is a proposition.
First we must prove that P ∨ false implies P. Assume a proof of P ∨ false.
Then, go into case analysis by applying the elimination rule for ∨ to that proof. 
To prove P implies P, assume a proof of P and then apply it. To resolve false implying P, 
assume a proof of false and then perform case analysis to show that it is not possible. 
Then, we must prove that P implies P ∨ false. Assume a proof of P, then use it with the introduction rule for 
∨ to prove P ∨ false.
QED.
-/


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
/-
Proof:
Assume P is a proposition.
First we must prove that P ∧ true implies P. Assume a proof of P ∧ true, then
apply the elimination rule for and to that proof to construct a proof of P. Then,
apply the proof of P to prove P.
Then, we must prove that P implies P ∧ true. Assume a proof of P, then split proving P ∧ true
into proving P and proving true individually. Apply the proof of P to prove P, then apply true.intro to
prove true.
QED.
-/


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

/-
Proof:
Assume P is a proposition.
First we must prove that P ∧ false implies false. Assume a proof of P ∧ false (paf),
then construct a proof of false using the elimination rule for and on paf. Apply the 
proof of false.
Then, we must prove that false inplies P ∧ false. We can show that this is not possible by applying
case analysis.
QED.
-/


