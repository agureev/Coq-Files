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

Definition true_to_app : bool -> (natlist -> (natlist  -> natlist)) :=
  fun b : bool => match b with
                  | true => app
                  | false => (fun x => fun y => y)
                  end.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | [ ] => [ ]
  | (h :: t) => true_to_app (odd h) ([h]) (oddmembers (t))
end.

                  
Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
simpl. reflexivity.

Definition countoddmembers : natlist -> nat :=
  fun l => length (oddmembers l).
Defined.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
 reflexivity. Defined.
Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
  reflexivity. Defined.
Example test_countoddmembers3:
  countoddmembers nil = 0.
reflexivity. Defined.


(*Definition alternate : natlist -> natlist -> natlist.
  intros l1 l2. induction l1, l2 as [| h1 t1 h2 t2].
  - exact ([ ]).
  - exact (h1 :: t1).
  - exact (n :: l1).
    - 
Defined.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
simpl. *)

      
Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | [ ], [ ] => [ ]
  | h1 :: t1, [ ] => h1 :: t1
  | [ ], h2 :: t2 => h2 :: t2
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: (alternate t1 t2)

  end.
Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
simpl. reflexivity. Defined.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
simpl. reflexivity. Defined. 
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
simpl. reflexivity. Defined.
Example test_alternate4:
  alternate [] [20;30] = [20;30].
simpl. reflexivity. Defined.

Definition bag := natlist.

Check eqb.

Definition true_to_succ : bool -> (nat -> nat) :=
  fun b => match b with
           | true => S
           | false => (fun x => x)
           end.


Fixpoint count (v : nat) (s : bag) : nat :=
  match v with
  | 0 => match s with
         | [ ] => 0
         | h :: t => match h with
                     | 0 => S (count 0 t)
                     | S n => count 0 t
                     end
                       end
         | S n => match s with
                  | [ ] => 0
                  | h :: t => match h with
                              | 0 => count (S n) t
                              | S n' => (fun x : bool => match x with
                                                         |true => S
                                                         |false => (fun x => x)
                                                         end)
                                                           (eqb n n') (count (S n) t)
                              end
                                end
                 
        
           end.
                  

Fixpoint count' (v : nat) (s : bag) : nat :=
  match v with
  | 0 => match s with
         | [ ] => 0
         | h :: t => match h with
                     | 0 => S (count 0 t)
                     | S n => count 0 t
                     end
                       end
         | S n => match s with
                  | [ ] => 0
                  | h :: t => match h with
                              | 0 => count (S n) t
                              | S n' => true_to_succ (eqb n n') (count (S n) t)
                              end
                                end
                 
        
           end.
                               

                                          
Example test_count1: count 1 [1;2;3;1;4;1] = 3.
simpl . reflexivity. Defined.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
simpl. reflexivity. Defined.

Definition sum : bag -> bag -> bag :=
  fun b => fun v => app b v. 

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
simpl. reflexivity.

Definition add (v : nat) (s : bag) : bag :=
  app [v] s.
Defined.


Example test_add1: count 1 (add 1 [1;4;1]) = 3.
simpl. reflexivity. Defined.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
simpl. reflexivity. Defined.

Search bool.

Definition member' (v : nat) (s : bag) : bool :=
  negb (0 =? count v s).

Fixpoint member (v : nat) (s : bag) : bool :=
  match s with
  | [ ] => false
  | h :: t => (v =? h) || (member v t)
                             end.

Example test_member1: member 1 [1;4;1] = true.
simpl. reflexivity. Defined.

Example test_member3: member 4 [1;4;1] = true.
simpl. reflexivity. Defined.

Example test_member2: member 2 [1;4;1] = false.
simpl. reflexivity. Defined.

Fixpoint remove_all (v : nat) (s : bag) : bag :=
  match v, s  with
  | 0, [ ] => [ ]
  | S n, [ ] => [ ]
  | 0, h :: t => match h with
                 | 0 => (remove_all 0 t)
                 | S m => (S m :: (remove_all 0 t))
                             end
                           
  | S n, h :: t => match h with
                  | 0 => S n :: (remove_all (S n) t)
                  | S m => ( fun x : bool => fun  y : nat  => fun  t : bag  => match x with
                                                                               | true => y :: t
                                                                               | false => t
                                                                               end ) (negb (eqb n m)) (S m) (remove_all (S n) t)
                   end
                     end.

Definition true_to_cons : bool -> nat -> bag -> bag :=
   fun x : bool => fun  y : nat  => fun  t : bag  => match x with
                                                     | true => y :: t
                                                     | false => t
                                                                               end.



                    
Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
reflexivity. Defined.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
reflexivity. Defined.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
reflexivity. Defined.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
reflexivity. Defined.

Fixpoint remove_one   (v : nat) (s : bag) : bag :=
  match v, s with
  | 0, [ ] => [ ]
  | S n, [ ] => [ ]              
           | 0, h :: t => match h with
                            |0 => t
                            |S n => S n :: (remove_one 0 t)
                          end
           | S n, h :: t => match h with
                            |0 => 0 :: (remove_one (S n) t)
                            | S m => (fun x : bool => fun t q : bag =>
                                        match x with
                                        | true => t
                                        | false => q
                                        end
                                     ) (andb (eqb n m) (negb (member (S n) t)))  t (h :: (remove_one (S n) t))
                            end
  end.

Fixpoint  remove_one_alt (v : nat) (s : bag) : bag :=
    match v, s with
  | _, [ ] => [ ]              
  | 0, h :: t => match h with
                            |0 => t
                            |S n => S n :: (remove_one_alt 0 t)
                          end
  | S n, h :: t => (fun x : bool => fun t q : bag =>
                                        match x with
                                        | true => t
                                        | false => q
                                        end
                                     ) (andb (eqb (S n) h) (negb (member (S n) t)))  t (h :: (remove_one_alt (S n) t))
                           
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
reflexivity. Defined. 
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
reflexivity. Defined. 
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
simpl. reflexivity. Defined. 
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
reflexivity. Defined.

Definition self_eq : forall (n : nat), (n =? n) = true.
  intro n. induction n.
  - simpl. reflexivity.
    - simpl. apply IHn.
Defined.

Definition add_inc_count (n : nat) (t : natlist) : count n (n :: t) = S (count n t).
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite (self_eq n). reflexivity.
Defined.

Definition app_nil_r : forall l : natlist, l ++ [] = l.
  intros l. induction l.
  - reflexivity.
  - simpl. rewrite IHl.
    reflexivity. Defined.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.

Definition app_assoc : forall  l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity. Defined.

Definition rev_app_distr : forall l1 l2 : natlist,
    rev (l1 ++ l2) = rev l2 ++ rev l1.
  intros l1 l2. induction l1.
  - simpl. rewrite (app_nil_r (rev l2)). reflexivity.
  - simpl. induction l2.
    + simpl. rewrite (app_nil_r (l1)). reflexivity.
    + simpl. rewrite IHl1. simpl. apply app_assoc. Defined.

Definition rev_involutive : forall l : natlist, rev (rev l) = l.
  induction l.
  - simpl. reflexivity.
  - simpl.  rewrite rev_app_distr. rewrite IHl. simpl. reflexivity.
Defined.

Definition app_assoc4 : forall l1 l2 l3 l4 : natlist,
    l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  intros l1 l2 l3 l4. rewrite app_assoc. rewrite app_assoc. reflexivity.
Defined.

Definition nonzeros_app : forall l1 l2 : natlist,
    nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
  intros l1 l2.
  induction l1.
  - simpl. reflexivity.
  - induction n.
    + simpl. apply IHl1.
    + simpl. rewrite IHl1. reflexivity.
Defined.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | [ ], [ ] => true
  | [ ], h2 :: t2 => false
  | h1 :: t1, [ ] => false
  | h1 :: t1, h2 :: t2 => andb (h1 =? h2) (eqblist t1 t2)
  end.

Example test_eqblist1 :
  (eqblist nil nil = true).
reflexivity. Defined.
Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
reflexivity. Defined.
Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
reflexivity. Defined.

Definition eqblist_refl (l: natlist) : true = eqblist l l.
  induction l.
  - reflexivity.
  - simpl. rewrite self_eq. rewrite  <- IHl. reflexivity. Defined.

Definition singleton_count (n : nat) : count n [n] = 1.
  induction n.
  -simpl. reflexivity.
- simpl. rewrite self_eq.
  reflexivity.
Defined.

Definition succ_geq_1 (n : nat) : leb 1 (S n) = true.
induction n.
- reflexivity.
- simpl. reflexivity.
Defined.


Definition count_member_nonzero (s : bag) (n : nat) :  1 <=? (count n (n :: s)) = true.
  induction s.
  - rewrite singleton_count.  simpl. reflexivity.
  - rewrite add_inc_count.  simpl. reflexivity.    
Defined.

Definition leb_n_Sn (n : nat) : n <=? (S n) = true.
  induction n.
  - simpl. reflexivity.
  - simpl. apply IHn.
Defined.

Definition empty_count (n : nat) : count n ([ ]) = 0.
  simpl. induction n. - reflexivity. - reflexivity. Defined.

Definition remove_empty (n : nat) : remove_one n ([ ]) = [ ].
  induction n. reflexivity. reflexivity. Defined.

Definition self_leq (n : nat) : (n <=? n) = true.
  induction n. simpl. reflexivity. simpl. apply IHn. Defined.

Inductive empty : Type := .
Search (_<?_).
Inductive unit : Type :=
  | point. 
                      

Definition transport {A : Type} (P : A -> Type) {x y : A} ( p : x = y) : P x -> P y.
  induction p. apply id. Defined.

Definition constr_contr_fun_nat : nat -> Type.
  intro n. induction n.
  exact unit. exact empty.
Defined.

Definition zero_leq_nat (n : nat) : 0 <=? n = true.
  induction n.
  - rewrite self_leq. reflexivity.
  - induction n.
    + simpl. reflexivity.
      + simpl. reflexivity.
Defined.
      
    

Definition inverse_path {A : Type} {x y: A} (p : x = y) : y = x.
  induction p. reflexivity. Defined.

Definition constr_contr_fun_bool : bool -> Type :=
  fun x => match x with
             |true => unit
                       |false => empty
                                  end.

Definition true_is_not_false (p : true = false): empty.
apply (transport constr_contr_fun_bool p).
exact point. Defined.

Definition plus_one_is_succ_l (n : nat) : 1 + n = S n.
  simpl. reflexivity. Defined.

Notation " x < y " := (x <? y = true).
Notation " x <= y" := (x <=? y = true).


Search (_ <=? _).

Definition succ_leq_one (x : nat) : S x <= 1 -> x <= 1.
induction x. - simpl. exact (fun x => x). - intro p. simpl. simpl in p. assert empty. + apply true_is_not_false. apply inverse_path. exact p. + induction H. Defined.

Definition nat_less_than_0_then_it_is_zero (x : nat) : x <= 0 -> x = 0.
  intro p. induction x. - reflexivity. - simpl in p. assert empty. apply true_is_not_false. + apply inverse_path. exact p. + induction H. Defined.

Definition  nat_less_than_0_then_it_is_zero_bool (x : nat) : x <= 0 -> x =? 0 = true.
  intro p. induction x. - reflexivity. - simpl in p. assert empty. apply true_is_not_false. + apply inverse_path. exact p. + induction H. Defined.

Definition one_is_not_zero  : (0 = 1) -> empty.
 intro p. apply (transport constr_contr_fun_nat p). exact point. Defined.


Definition leq_zero_then_zero ( m : nat) : m <=? 0  = true -> m = 0.
  intro p. induction m. - reflexivity. -  simpl in p. assert empty. apply true_is_not_false.  apply inverse_path. exact p. induction H. Defined.

Definition eq_then_leq (m n : nat) : m = n -> m <= n.
  intro p. induction p. apply self_leq. Defined.

Inductive Sigma (A : Type) (B : A -> Type) : Type :=
| deppair : forall (x : A), B x -> Sigma A B.

Search (_ + _).

Definition plus_pres_eq (n m k : nat) : (n = m -> n + k = m + k ).
  intro p. induction p. reflexivity. Defined.

Definition fun_ap_eq {A B : Type} {x y : A} (f : A -> B) : x = y -> f x = f y.
  intro p. induction p. reflexivity. Defined.

Definition S_is_inj (n m : nat) : S n = S m -> n = m.
intro p. exact (fun_ap_eq pred p). Defined.

Definition plus_is_inj (n m k : nat) : (n + k = m + k -> n = m).
intro p. induction k.  - Search (_ + 0). rewrite (add_0_r n) in p. rewrite (add_0_r) in p. exact p. - Search ( _ + (S _)). rewrite <- plus_n_Sm in p. rewrite <- plus_n_Sm in p. assert (n + k = m + k). + apply S_is_inj, p. + apply IHk, H. Defined.                                                                    

Definition nat_is_not_succ_nat (n : nat) : (n = S n) -> empty.
  intro p. induction n. - apply one_is_not_zero. exact p. - simpl in p.  apply IHn. apply S_is_inj, p. Defined.
  
Definition zero_is_not_succ (n : nat) : (0 = S n) -> empty.
intro p. induction n. + apply one_is_not_zero. exact p. + assert (S (S n) = 0). - apply leq_zero_then_zero. assert (S (S n) = 0). apply inverse_path, p. exact (eq_then_leq (S (S n)) (0) H).  -  apply IHn. apply (fun_ap_eq pred p). Defined.

Definition succ_eq (n : nat) (p : 1 = S n) : n = 0.
  induction n.
  - reflexivity.
  - simpl in p.  simpl in p. apply inverse_path. apply (fun_ap_eq pred p). Defined.

Fixpoint count_alt (v : nat) ( s : bag) : nat :=
  match s with
  | [ ] => 0
  | h :: t => true_to_succ (eqb h v)  (count_alt v t)
                           end.

Definition one_count_alt_singleton : forall (n : nat), count_alt n [ n ] = 1.
intro n. induction n. - reflexivity. - simpl. rewrite self_eq. simpl. reflexivity. Defined.

Definition one_count_singleton : forall (n : nat), count n [n] = 1.
  intro n. induction n. - reflexivity. - simpl. rewrite (self_eq n). reflexivity. Defined.

Definition empty_induction_tactic {A : Type} : empty -> A.
  intro x. induction x. Defined.





Fixpoint included (s1 s2 : bag) : bool :=
  match s1, s2 with
  | [ ], _ => true
  | h :: t, [ ] => false
  | h1 :: t1, h2 :: t2 => (included t1 (h2 :: t2)) && (member h1 (h2 :: t2) && (count h1 (h1 :: t1) <=? count h1 (h2 :: t2)))
  end.

Example test_included_alt1 : included [1;1] [1] = false.
simpl. reflexivity. Defined.
Example test_included1: included [1;2] [2;1;4;1] = true.
 simpl. reflexivity. Defined.
Example test_included2: included [1;2;2] [2;1;4;1] = false.
 simpl. reflexivity. Defined.
(* Definition bag_count_sum (s l : bag) (n : nat) : count n ( s ++ l ) = count n (s) + count n l.
  induction s. rewrite empty_count. simpl. reflexivity.  induction l. - rewrite empty_count. rewrite <- plus_n_O. Search (_ + 0). rewrite empty_count in IHs. rewrite <- plus_n_O in IHs. Abort. *)

Inductive natoption : Type :=
  | Some (n : nat)
| None.

Inductive id : Type :=
| Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 =>  n1 =? n2
  end.


Definition eqb_id_refl : forall x, eqb_id x x = true.
  intro x. induction x. induction n.  - simpl. reflexivity.
                                        - simpl. simpl in IHn. assumption.
Defined.



Inductive partial_map : Type :=
  | Empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | Empty => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.

Definition update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.

  intros d x v. induction d. - simpl. rewrite eqb_id_refl. reflexivity.
  - simpl. rewrite eqb_id_refl. reflexivity.
Defined.

Definition  update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
  intros d x y o. intro p. induction d. - simpl. rewrite p. reflexivity. - simpl.  rewrite p. rewrite <-  IHd. simpl.
                                                                           reflexivity.
Defined.
