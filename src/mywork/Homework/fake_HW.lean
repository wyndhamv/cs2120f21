--1
example : 0 ≠ 1 :=
begin
  show ¬ (0=1),
  assume p,
  contradiction,
end

--2
example : 0 ≠ 0 → 2 = 3:=
begin
  assume h,
  have g : (0 = 0) := eq.refl 0,
  have f : false := h g,
  cases f,  

  --or can just assume h then exact false.elim (h (eq.refl 0))
end

--3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume p,
  show ¬(P) → false,
  assume np,
  have f : false := np p,
  contradiction,
end

#check classical.em
open classical
#check em

axiom em : ∀ (p : Prop), p ∨ ¬p

--4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume nnp,
  have ponp : (P ∨ ¬P) := classical.em P,
  apply or.elim ponp,

  assume p,
  exact p,

  assume np,
  contradiction,
end

--5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∧ ¬ Q :=
begin
  assume P Q,
  apply iff.intro _,

  --forwards
    assume npanq,
    show P ∧ Q → false,
    assume paq,
    have np := and.elim_left npanq,
    have p := and.elim_left paq,
    contradiction,

  --backwards
    assume npaq,
    show ((P → false) ∧ (Q → false)),
    
    

end


--6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q ) → ¬ P ∨ ¬ Q :=
begin

end
