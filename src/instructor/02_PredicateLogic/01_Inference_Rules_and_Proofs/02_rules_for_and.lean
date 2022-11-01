/- *** AND *** -/

-- ∧ 
def and_introduction  : Prop  := ∀ (X Y : Prop), X → Y → (X ∧ Y)
def and_elim_left     : Prop  := ∀ (X Y : Prop), X ∧ Y → X  
def and_elim_right    : Prop  := ∀ (X Y : Prop), X ∧ Y → Y  

/-
Note that we are able to express these rules of logic very
naturally in higher-order constructive logic because we can
quantify over propositions. You cannot write these definitions
in first-order logic because it doesn't allow you to do this.
Such an expression is a syntax error in first-order logic. 
-/
theorem and_intro_true : and_introduction :=
begin
unfold and_introduction,
assume X Y,
exact and.intro,

end
