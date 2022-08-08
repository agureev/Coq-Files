From AG Require Export Induction.

Check nat_to_bin.



  Inductive natprod : Type :=
  | pair : nat -> nat -> natprod.

  Check (pair 3 5).

  Definition p_1 (p : natprod) : nat :=
    match p with
    | pair x y => x
    end.

  Definition p_2 (p : natprod) : nat :=
    match p with
    | pair x y => y
    end.

  Compute (p_1 (pair 3 5)).

  Notation "( x , y )" := (pair x y).

  Definition swap_pair (p : natprod) : natprod :=
    match p with
    | (x, y) => (y, x)
                  end.

  Definition surjective_pairing : forall p : natprod, p = ( p_1 p, p_2 p).
    intros [x y]. simpl. reflexivity.
  Defined.

  Definition snd_fst_is_swap : forall (p : natprod), (p_2 p, p_1 p) = swap_pair p.
    intros [x y]. simpl. reflexivity.
    Defined.

  Definition fst_swap_is_snd : forall (p : natprod),
      p_1 (swap_pair p) = p_2 p.
    intros [x y]. simpl. reflexivity.
  Defined.

  Inductive natlist : Type :=
  | nil
  | cons (n : nat) (list : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                       (right associativity, at level 60).

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.
Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: l => match h with
              | 0 => (nonzeros l)
              | S n => ([S n] ++ nonzeros l)
              end
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
simpl.  reflexivity.
Defined.

Search bool.

Inductive typeprod (A B : Type) : Type :=
  | termpair : A -> B -> typeprod A B.

Definition eq_check (A B : Type) (a1 a2 : A) (b1 b2 : B) (p : a1 = a2) (q : b1 = b2) : (termpair _ _ a1 b1) = (termpair _ _  a2 b2).
induction p. induction q. reflexivity. Defined.

Definition  tru _nil : nat -> natlist :=
  fun n => match n with
           | 0 => nil
                    | S 

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match h with
              | 0 => (oddmembers t)
                       | S n => 

                           
