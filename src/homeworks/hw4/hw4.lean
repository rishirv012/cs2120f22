/-
CS 2120 F22 Homework #4. Due Oct 13.
-/

/- #1A [10 points]

Write a formal proposition stating that 
logical and (∧) is associative. That is, 
for arbitrary propositions, P, Q, and R,
P ∧ (Q ∧ R) is true *iff* (P ∧ Q) ∧ R is, 
too. Replace the placeholder (_) with your
answer.
-/

def and_associative : Prop :=
  ∀(P Q R: Prop), (P ∧ Q) ∧ R  ↔ P ∧ (Q ∧ R) 



/- #1B [10 points]

Give an English language proof. Identify
the inference rules of predicate logic
that you use in your reasoning.
-/

/-
Answer: Given the bi-implication, we can split it into two seperate implications using
iff.intro, we then need to prove each of the two cases. We start by breaking apart the 
first case using case analysis as well as and elimination on the left and right. This
will ultimately give us P Q and R as individual propositions but I believe it would 
still be unsolveable as the result we're trying to prove would be a multi proposition
statement. So, we could need to apply and introduction twice to break apart the result of
P ∧ Q ∧ R into P Q R. After this we just use the exact function to eliminate the three
cases of P Q and R. Like I said at the beginning, using iff.intro creates two major cases 
so we would just repeat this entire process again to deal with the second case. 
-/

/- #1C [5 points]
-/

theorem and_assoc_true : and_associative :=
begin
unfold and_associative,
assume P Q R,
apply iff.intro,
assume h,
cases h,
let p := and.elim_left h_left,
let q := and.elim_right h_left,
apply and.intro,
exact p,
apply and.intro,
exact q,
exact h_right,
assume h,
cases h,
let q := and.elim_left h_right,
let r := and.elim_right h_right,
apply and.intro,
apply and.intro,
exact h_left,
exact q,
exact r,
end

/- #2A [10 points]
Write the proposition that ∨ is associative.,
analogous to the proposition about ∧ in #1.
-/
def or_associative : Prop := 
  ∀(P Q R: Prop), (P ∨ Q) ∨ R  ↔ P ∨ (Q ∨ R) 
/- #2B [10 points]
Write an English language proof of it, citing
the specific inference rules you use in your
reasoning.
I start by unfolding or_associative and then assuming P Q R as propositions to use later,
then I will apply iff.intro to split the bi-implication into two normal implications. 
After that I can start working on the first of the two cases this creates. To start I 
assume h and create two cases with it, the first of them being P ∨ Q and the second being 
R. With these two subcases I can apply or intros to break them down into P and Q individually
and then just use exact to satisfy the goal. That takes care of the first case created
from splitting the bi-implication. To satisfy the second one, I repeat the same process over 
again.
-/

/- #2C [5 points]
Complete the following formal proof.
-/

theorem or_associative_true : or_associative :=
begin
unfold or_associative, 
assume P Q R,  
apply iff.intro,
assume h,
cases h with pq r,
cases pq,
apply or.intro_left,
exact pq,
apply or.intro_right,
apply or.intro_left,
exact pq,
apply or.intro_right,
apply or.intro_right,
exact r,
assume h,
cases h with p rq,
apply or.intro_left,
apply or.intro_left,
exact p,
cases rq with q r,
apply or.intro_left,
apply or.intro_right,
exact q,
apply or.intro_right,
exact r,
end


/- #3A [10 points]
Write a formal statement of the proposition.
-/

def arrow_transitive : Prop :=
  ∀(X Y Z: Prop), (X → Y) → (Y → Z) →(X → Z)  


/- #3B [10 points]

Write an English language proof of the proposition
that for any propositions, X, Y, and X, it's the
case that (X → Y) → (Y → Z) → (X → Z). In other
words, implication is "transitive." Hint: Recall
that if you have a proof of, say, X → Y, and you 
have a proof of X, you can derive a proof of Y by
arrow elimination. Think of it as applying a proof
of an implication to a proof of its premise to get
yourself a proof of its conclusion.

I can start by unfolding the arrow transitive proposition and then assuming X Y and Z as 
propositions. I can then assume xy, yz, and x, which will give me proofs that X → Y, 
Y → Z, and a proof of X. With the proof of X → Y and the proof of X, I can derive a proof
of Y using arrow elimination with a let function. In the same manner, I can derive a proof
of Z by using arrow elimination on the proof of Y → Z and the proof of Y. Once I have a proof
of Z, the goal will be met. 

-/


/- #3C [5 points]. 
Write a formal proof of it.
-/
theorem arrow_transitive_true : arrow_transitive :=
begin
unfold arrow_transitive,
assume X Y Z, 
assume xy,
assume yz,
assume x,
let y := (xy x),
let z := (yz y),
exact z,

end


/- #4
Suppose that if it's raining then the streets
are wet. This problem requires you to prove that
if the streets are not wet then it's not raining.

if raining then wet
-/

/- #4A [10 points]

Start by writing the proposition in predicate
logic by completing the following answer.
-/

def contrapositive : Prop :=
  ∀ (Raining Wet : Prop), 
    (Raining → Wet) → (¬Wet → ¬Raining)


/- #4B [10 points]. 
-/

theorem contrapositive_valid : contrapositive :=
begin
unfold contrapositive, 
assume r w, 
assume rw,
assume nw,
assume r,
let w := (rw r),
contradiction,

end

/- #4C [5 points]. 

Give an English language proof of it.
I start by unfolding the contrapositive and then breaking it into pieces. I can assume r
and w to get my starting propositions. Then I can get a proof of r → w by doing another 
assume that takes a first part of the contrapositive as well as a proof of ¬w with 
another assume that takes the next part of the contrapositive. I'm left with ¬r as my 
result which I can seperate into a proof of r and a false left in my result. Then I just
use arrow elimination to create a proof of W using r → w and the proof of r I have. This
leaves me with a proof of w AND ¬w which is impossible so I can finish the theorem with 
a contradiction. 
-/

/- #5. Extra credit.

Complete the following formal proof of the 
proposition that if for any proposition P, 
P ∨ ¬P is true, then for any propositions, 
X and Y, if it's not the case that X or Y
is true then it is the case that ¬X and ¬Y 
is true. 
-/

theorem demorgan1 : 
  (∀ (P : Prop), P ∨ ¬ P) → 
    ∀ (X Y : Prop), 
      ¬(X ∨ Y) → (¬X ∧ ¬Y) :=
begin
assume em X Y nxory,
cases (em X) with x nx,
let foo := or.intro_left Y x,

end

/-
A comment on or.intro_left and or.intro_right.
In Lean each of these takes two arguments: a
proof of the disjunct -- the proposition on 
one side of the ∨ -- that is to be proven true, 
*and* it takes as an argument the proposition 
that is not being proven true. In applications 
of these rules the proposition argument (not 
being proven) comes first, while the proof 
argument comes second.

The reason is that Lean needs to know what 
overall proposition is being proved. From the
proof argument it can infer the proposition 
being proved, but it needs the other proposition
as well to know the full (X ∨ Y) disjunction to
be proved. 

Here's an example:
-/

example : 0 = 0 ∨ 0 = 1 :=
begin
apply or.intro_left (0 = 1) rfl
/-
The "rfl" serves as a proof of 0=0.
But in addition, as the first argument
to or.intro, we need to provide the
*proposition* that is not being proved.
Here's that's (0 = 1). In contexts
where Lean can infer both disuncts,
you can use the simpler or.inl or 
or.inr, each of which just takes one
argument: a proof of the left or of 
the right side, respectively.
-/
end

