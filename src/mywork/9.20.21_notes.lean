-- Using ¬ 

example : false :=
begin
end

example : ¬ false :=
begin
  assume f,
  exact f,
end

example : ¬ 0 = 1 :=
begin
  assume h,
end


example : ∀ (P Q R : Prop), P ∨ Q → R :=
begin
  assume P Q R,
  assume pq,
  cases pq,

end

example : true → true :=
begin
  assume t,
  cases t,
  exact true.intro,
end

example : ¬ (0=1) :=
begin
  assume h,
  cases h,
end

example : false → false :=
begin
  assume f,
  cases f,  --or exact false.elim f
end

theorem false_elim (P : Prop) (f : false) : P :=
begin
  exact false.elim f,
end