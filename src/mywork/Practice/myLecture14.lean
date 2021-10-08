axioms
  (Person : Type)
  (Likes : Person → Person → Prop)

example :
  ¬ (∀ p : Person, Likes p p ) ↔ 
  ∃ p : Person, ¬ Likes p p :=
begin
  apply iff.intro,
  assume h,
  have f := classical.em (∃ (p : Person), ¬Likes p p),
  cases f,
  exact f,


  have contra : ∀ (p : Person), Likes p p := _, 
  contradiction,

  assume p,

  have g := classical.em (Likes p p),
  cases g,

  exact g,
  
  have a : ∃(p : Person), ¬Likes p p := exists.intro p g,
  contradiction,
  

end