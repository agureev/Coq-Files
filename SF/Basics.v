Inductive bool : Type :=
| true
| false.


Definition negb (b:bool) : bool :=
match b with
  | true => false
  | false => true
end.

Definition andb (b1:bool) (b2:bool) : bool :=
    match b1 with
    | true => b2
    | false => false
    end.

Definition orb (b1:bool) (b2:bool) : bool :=
        match b1 with
        | true => true
        | false => b2
        end.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Definition negb' (b:bool) : bool :=
    if b then false
    else true.


Definition andb' (b1:bool) (b2:bool) : bool :=
        if b1 then b2
        else false.
Definition orb' (b1:bool) (b2:bool) : bool :=
        if b1 then true
        else b2.

(*Exercise 1*)

Definition nandb (b1:bool) (b2:bool) : bool :=
match b1 with
      | false => true
      | true => (negb b2)
end.

Example test_nandb1: (nandb true false) = true.
simpl. reflexivity.  Defined.

Example test_nandb2: (nandb false false) = true.
simpl. reflexivity. Defined.
Example test_nandb3: (nandb false true) = true.
simpl. reflexivity. Defined.
Example test_nandb4: (nandb true true) = false.
simpl. reflexivity. Defined.


(*Exercise 2*)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
match b1 with
    | true => (andb b2 b3)
    | false => false
end.

Example test_andb31: (andb3 true true true) = true.
simpl. reflexivity. Defined.
Example test_andb32: (andb3 false true true) = false.
simpl. reflexivity. Defined.
Example test_andb33: (andb3 true false true) = false.
simpl. reflexivity. Defined.
Example test_andb34: (andb3 true true false) = false.
simpl. reflexivity. Defined.

Check true.

Inductive rgb : Type :=
  | red
  | green
  | blue.
Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).


(*Alternative*)
Inductive color' : Type :=
  | black'
  | white'
  | primary' : rgb -> color'.

Definition monochrome (c : color) : bool :=
    match c with
    | black => true
    | white => true
    | primary p => false
    end.

Definition isred (c : color) : bool :=
        match c with
        | black => false
        | white => false
        | primary red => true
        | primary _ => false
        end.

Module Playground.
Definition b : rgb := blue.
End Playground.
Definition b : bool := true.
Check Playground.b : rgb.
Check b : bool.

Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).

Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.

End NatPlayground.

Check (S (S (S (S O)))).
(* ===> 4 : nat *)

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

(*Note: Fixpoint allows for recursive definitions*)
Fixpoint even (n:nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S (S n') => even n'
    end.

Definition odd (n:nat) : bool :=
        negb (even n).

Module NatPlayground2.
  Fixpoint plus (n : nat) (m : nat) : nat :=
          match n with
          | O => m
          | S n' => S (plus n' m)
          end.

  Fixpoint mult (n m : nat) : nat :=
            match n with
            | O => O
            | S n' => plus m (mult n' m)
            end.
  Fixpoint minus (n m:nat) : nat :=
            match n, m with
            | O , _ => O
            | S _ , O => n
            | S n', S m' => minus n' m'
            end.
End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
                  match power with
                  | O => S O
                  | S p => mult base (exp base p)
                  end.

(*Exercise 3*)
Fixpoint factorial (n:nat) : nat :=
    match n with
        | O => S O
        | S n' => mult (S n') (factorial n')
    end.

Example test_factorial1: (factorial 3) = 6.
simpl. reflexivity. Defined.
Example test_factorial2: (factorial 5) = (mult 10 12).
simpl. reflexivity. Defined.
Example test_factorial3: (factorial 1) = 1.
simpl. reflexivity. Defined.


Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Fixpoint leb (n m : nat) : bool :=
                        match n with
                        | O => true
                        | S n' =>
                            match m with
                            | O => false
                            | S m' => leb n' m'
                            end
                        end.

Fixpoint eqb (n m : nat) : bool :=
                            match n with
                            | O => match m with
                                   | O => true
                                   | S m' => false
                                   end
                            | S n' => match m with
                                      | O => false
                                      | S m' => eqb n' m'
                                      end
                            end.


Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

(*Exercise 4*)

Definition ltb (n m : nat) : bool :=
    match n, m with
    | O, O => false
    | O, _ => true
    | S n', O => false
    | S n', S m' => leb (S n') (m')
    end.

Example test_ltb1: (ltb 2 2) = false.
simpl. reflexivity. Defined.
Example test_ltb2: (ltb 2 4) = true.
reflexivity. Defined.
Example test_ltb3: (ltb 4 2) = false.
reflexivity. Defined.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.


Definition ltb_alt (n m : nat) : bool :=
negb (m - n =? O).
(*This one does not simplify internally*)

    Example test_ltb1_alt: (ltb_alt 2 2) = false.
    reflexivity. Defined.
    Example test_ltb2_alt: (ltb_alt 2 4) = true.
    reflexivity. Defined.
    Example test_ltb3_alt: (ltb_alt 4 2) = false.
    reflexivity. Defined.


Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Defined.

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
  Proof.
    intros n m.
    intros H.
    rewrite -> H. (*the arrow tells where we are transporting the proof to*)
    reflexivity. Defined.
(*rewrite is used as automatic transport*)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
intros n m o p q.
rewrite p. (*rewrite automatically transports to the right*) 
rewrite q. reflexivity. Defined.

Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.


Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
intro p. rewrite <- mult_n_Sm. rewrite <- mult_n_O. simpl. reflexivity. Defined.

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  (*The annotation "as [| n']" is called an intro pattern. 
  It tells Coq what variable names to introduce in each subgoal. 
  In general, what goes between the square brackets is a list of lists of names, 
  separated by |. In this case, the first component is empty, 
  since the O constructor is nullary (it doesn't have any arguments). 
  The second component gives a single name, n', since S is a unary constructor.
In each subgoal, Coq remembers the assumption about n that is relevant for this subgoal -- either n = 0 or n = S n' for some n'. The eqn:E annotation tells destruct to give the name E to this equation.*)
- simpl. reflexivity.
- simpl. reflexivity.
Defined.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.

  Theorem andb_commutative : forall b c, andb b c = andb c b.
  Proof.
    intros b c. destruct b eqn:Eb.
    - destruct c eqn:Ec.
      + reflexivity.
      + reflexivity.
    - destruct c eqn:Ec.
      + reflexivity.
      + reflexivity.
  Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
  intros b c H.
  destruct b eqn:E1.
  - destruct c eqn:E2.
    + reflexivity.
    + simpl in H. apply H.
  - destruct c eqn:E2.
    + reflexivity.
    + simpl in H. apply H.
Defined.

Theorem plus_1_neq_0' : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity. Qed.

(*Exercise 5*)
Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
intros [|n].
- simpl. reflexivity.
- simpl. reflexivity.
Defined.


(*Additional Exercises*)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.

intros f H b. rewrite (H b). rewrite (H b). reflexivity. Defined.

Theorem negation_fn_applied_twice:
 forall (f : bool -> bool),
 (forall (x : bool), f x = negb x) ->
 forall (b : bool), f (f b) = b.
 intros f H b. rewrite (H b). rewrite (H (negb b)). apply negb_involutive. Defined.

 Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.

intros [|] [|] H.  
- reflexivity. - simpl in H. rewrite H. reflexivity.
- simpl in H. exact H. - reflexivity. Defined.


Theorem andb_eq_orb' :
forall (b c : bool),
(andb b c = orb b c) ->
b = c.
intros [|] c H. simpl in H. - rewrite H. reflexivity.
- simpl in H. exact H. Defined.

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Axiom nul_z : B0 Z = Z.

Fixpoint incr (m:bin) : bin :=
    match m with
    | Z => B1 Z
    | B0 n => B1 n
    | B1 n => B0 (incr n)
    end.

    Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
    reflexivity. Defined.
    Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
    reflexivity. Defined.
Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
     simpl. simpl. reflexivity. Defined.

Fixpoint bin_to_nat (m:bin) : nat :=
    match m with
    | Z => O
    | B0 m' => 2 * (bin_to_nat m')
    | B1 m' => 2 * (bin_to_nat m') + 1
    end.

Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
  simpl. reflexivity. Defined.
Example test_bin_incr5 : bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
  simpl. reflexivity. Defined.
Example test_bin_incr6 : bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
  simpl. reflexivity. Defined.

Check bin_to_nat.
    
