
Inductive N : Type :=
  | zero : N 
  | succ : N -> N.
Inductive CoProd (A B : Type) : Type :=
  | inl : A -> CoProd A B 
  | inr : B -> CoProd A B.
Inductive Prod (A B : Type) : Type :=
  | pair : A -> B -> Prod A B.
Notation "A + B" := (CoProd A B) (at level 50, left associativity).
Notation "A × B" := (Prod A B) (at level 50, left associativity).
Definition pr1 {A : Type} {B : Type} (x : A × B) : A.
    induction x. exact a. Defined.
Definition pr2 {A : Type} {B : Type} (x : A × B) : B.
    induction x. exact b. Defined.
Inductive Σ (A : Type) (B : A -> Type) : Type :=
  | deppair : forall (x : A), (B x -> Σ A B).

Definition proj1  {A : Type} {B : A -> Type} (x : Σ A B) : A.
  induction x. exact x. Defined.
Definition proj2 {A : Type} {B : A -> Type} (x : Σ A B) : B (@proj1 _ B x).
  induction x. simpl. exact b. Defined.

Inductive unit : Type :=
  | one .

Inductive empty : Type :=
  .


Inductive eq_alt {A : Type} : A -> A -> Type :=
  | refl (x : A):  eq_alt x x .
Notation "a ≡ b" := (eq_alt a b) (at level 50, left associativity).

Definition proj1_test {A : Type} {B : A -> Type} (x : A) (y : B x) :
proj1 (deppair _ _ x y) ≡ x.
simpl. apply refl. Defined.

 (*Chapter 2.1*)
Definition inverse_path {A : Type} {a b : A}: a ≡ b -> b ≡ a.
    intro p. induction p. apply refl. Defined.


Notation "p ^-1" := (inverse_path p) (at level 55, left associativity).

Definition concat  {A : Type} {x y z : A} : 
(x ≡ y) -> (y ≡ z) -> (x ≡ z).
    intros p q. induction p. induction q. apply refl. Defined.
Notation "p ⋅ q" := (concat p q) (at level 50, left associativity).

Definition composition {A B C: Type} (f : A -> B) (g : B -> C) : A -> C.
intro a. exact (g (f a)). Defined.

Notation "g ∘ f" := (composition f g) (at level 50, left associativity).
Definition id (A : Type) : A -> A := fun a => a.
Definition transport {A : Type} {B : A -> Type} {x y : A} (p : x ≡ y) : B x -> B y.
induction p. exact (fun a => a). Defined.
Definition id_transp {A : Type} {x y : A}  (p : x≡y): 
@transport A (fun a => (x ≡ a)) (x) (y) (p) (@refl (A) (x)) ≡ p.
induction p. simpl. exact (@refl (x ≡ x) (refl x)).
Defined.
(*Lemma 2.1.4.*)
Definition refl_concat_right {A : Type} {x y : A} (p : x ≡ y):
(p ⋅ refl y) ≡ p.
induction p. simpl. apply refl. Defined.
Definition refl_concat_left {A : Type} {x y : A} (p : x ≡ y):
(refl x ⋅ p) ≡ p.
induction p. simpl. apply refl. Defined.
Definition path_inverses_cancel_left  {A : Type} {x y : A} (p : x ≡ y) :
p ⋅ (p ^-1) ≡ refl x.
induction p. simpl. apply refl. Defined.
Definition  path_inverses_cancel_right  {A : Type} {x y : A} (p : x ≡ y) :
(p ^-1) ⋅ p ≡ refl y.
induction p. simpl. apply refl. Defined.
Definition double_path_inv_cancels   {A : Type} {x y : A} (p : x ≡ y):
(p ^-1) ^-1 ≡ p.
induction p. simpl. apply refl. Defined.
Definition concat_assoc  {A : Type} {x y z w : A} (p : x ≡ y) 
(q : y ≡ z) (r : z ≡ w): ((p ⋅ q) ⋅ r) ≡ (p ⋅ (q ⋅ r)).
induction p. induction q. induction r. simpl. apply refl. Defined.


(* Chapter 2.2*)

Definition ap {A B : Type} (f : A -> B) {x y : A} : x ≡ y -> f x ≡ f y.
intro p. induction p. exact (refl (f x)). Defined.

(*Lemma 2.2.2.*)
Definition  ap_concat {A B C: Type} (f : A -> B) (g : B -> C) {x y z: A} (p : x ≡ y) 
(q : y ≡ z) : ap f (p ⋅ q) ≡ ((ap f p) ⋅ (ap f q)).
induction p. induction q. simpl. apply refl. Defined.

Definition  ap_inv {A B C: Type} (f : A -> B) {x y: A} (p : x ≡ y) :
ap f (p ^-1) ≡ ((ap f p) ^-1).
induction p. simpl. apply refl. Defined.

Definition ap_compose  {A B C: Type} (f : A -> B) (g : B -> C) {x y: A} (p : x ≡ y):
(ap g (ap f p)) ≡ ap (g ∘ f) p.
induction p. simpl. apply refl. Defined.

Definition ap_id {A : Type} {x y : A} (p : x ≡ y) : ap (id A) p ≡ p.
induction p. simpl. apply refl. Defined.

Definition lift {A : Type} {P : A -> Type} {x y : A} (u : P x) (p : x ≡ y) : 
(@deppair A P (x) (u)) ≡ (@deppair A P (y) (transport p u)).
 induction p. apply refl. Defined.

Definition ap_dep {A : Type} {P : A -> Type} (f : forall (x : A), P x) {x y : A} (p : x ≡ y):
transport (p) (f x)  ≡ f y.
induction p. simpl. apply refl. Defined.

Definition ap_refl {A B: Type} {f : A -> B} {x: A} : ap  f (refl x) ≡ refl (f x).
simpl. apply refl. Defined.


Definition const_fam {A : Type} (B : Type) : A -> Type.
intro p. exact B. Defined.


Definition transportconst {A : Type} {B : Type}
{x y : A} (p : x ≡ y) (b :  (@const_fam A B x)): (@transport A (@const_fam A B) x y p b) ≡ b.
induction p. simpl. apply refl. Defined.

(*Lemma 2.3.8.*)

(*Definition ap_dep_and_transpconst {A : Type} {B : Type} (f : A -> B) {x y : A} (p : x ≡ y)
: (ap_dep f p) ≡ (@transportconst A B x y p (f x)) ⋅ (ap f p). *)

(*Lemma 2.3.9*)
Definition transpot_concat {A : Type} {P : A -> Type} {x y z : A} {u : P x} (p : x ≡ y) 
(q : y ≡ z) : transport q (transport q u) ≡ transport (p ⋅ q) u.
induction p. induction q. simpl. apply refl. Defined.

Definition  transport_compose_ap {A B : Type} {P : B -> Type} (f : A -> B) {x y : A} {u : P  (f x)} (p : x ≡ y) 
 : @transport A (P ∘ f) _ _ p u ≡ @transport B P _ _ (ap f p) u.
 induction p. simpl. apply refl. Defined.

Definition transport_dep_types {A : Type} (P Q : A -> Type) (f : forall (x : A), P x -> Q x)
{x y : A} (p : x ≡ y) (u : P x) : @transport A Q _ _ (p) (f x u) ≡ f y (@transport A P x y p u).
induction p. simpl. apply refl. Defined.


(* Chapter 2.4*)

Definition fib {A :Type} {B : Type} (f : A -> B) (y : B) : Type :=
 Σ A (fun x => f(x) ≡ y).

Definition homotopic {A B : Type} (f g: A -> B) : Type :=
    forall (x : A), f x ≡ g x.

Notation "f ~ g" := (homotopic f g) (at level 50, left associativity).

Definition homotopy_ref {A : Type} (f : A -> A): f ~ f. 
intro a. apply refl. Defined.

Definition homotopy_sym {A B : Type} {f g : A -> B} (p : f ~ g) : g ~ f.
intro a. apply ((p a) ^-1). Defined.

Definition homotopy_trans {A B : Type} {f g h : A -> B} (p : f ~ g) (q : g ~ h): f ~ h.
intro a. apply ((p a) ⋅ (q a)). Defined.

(*Lermma 2.4.3*)

Definition homotopy_naturality {A B : Type} {x y : A} (p : x ≡ y) {f g : A -> B} (H : f ~ g)
: ((H x) ⋅ (ap g p)) ≡ ((ap f p) ⋅ (H y)).
induction p. apply ( (refl_concat_right (H x)) ⋅ ((refl_concat_left (H x) ) ^-1)). Defined.

(*Lemma 2.11.2*)
Definition transport_concat {A : Type} {a x1 x2: A} {p : x1 ≡ x2} {q : a ≡ x1}
: @transport A (fun y => a ≡ y) _ _ (p) q ≡ (q ⋅ p).
induction p. induction q. simpl. apply refl. Defined.

Definition transport_inverse_concat  {A : Type} {a x1 x2: A} {p : x1 ≡ x2} {q : x1 ≡ a}
: @transport A (fun y => y ≡ a) _ _ (p) q ≡ ((p) ^-1 ⋅ q).
induction p. induction q. simpl. apply refl. Defined.

Definition transport_diagonal  {A : Type} {x1 x2: A} {p : x1 ≡ x2} {q : x1 ≡ x1}
: @transport A (fun y => y ≡ y) _ _ (p) q ≡ ((p) ^-1 ⋅ q ⋅ p).
induction p. simpl. induction q. simpl. apply refl. Defined.

Definition isequiv {A B : Type} (f : A -> B) : Type :=
      (Σ (B -> A) (fun (g : B -> A) => f ∘ g ~ id B)) × (Σ (B -> A) (fun (g : B -> A) => g ∘ f ~ id A)).
      
Definition equivalent (A B : Type) : Type :=
    Σ (A -> B) (fun f => isequiv f).

Notation "A ≃ B" := (equivalent A B) (at level 50, left associativity).

Definition isProp (A : Type) : Type :=
   forall (x y : A), x ≡ y.


Definition Σ_equivalnce_forward {A : Type} {P : A -> Type} (z w : Σ A P) : 
   (z ≡ w) -> Σ (proj1 z ≡ proj1 w) (fun p => (transport p (proj2 z)) ≡ (proj2 w)).
   intro p. induction p. simpl. 
   exact (deppair ((proj1 x ≡ proj1 x)) 
   ((fun p : proj1 x ≡ proj1 x => transport p (proj2 x) ≡ proj2 x)) 
   (refl (proj1 x)) (refl (proj2 x))). Defined.

Definition Σ_equivalence_backward {A : Type} {P : A -> Type} (z w : Σ A P) :
Σ ((proj1 z) ≡ (proj1 w)) 
(fun p => (@transport (A) P _ _ p (proj2 z)) ≡ (proj2 w)) 
-> (z ≡ w).
intro y. induction y. induction z. simpl. induction w. simpl in x.
simpl in b. induction x. simpl in b. induction b. apply refl. Defined.

Definition Σ_equivalence_composition_backward  {A : Type} {P : A -> Type} (z w : Σ A P):
 (Σ_equivalnce_forward z w) ∘ (Σ_equivalence_backward z w) ~ (id _).
 intro x. induction z. induction w. simpl in x. simpl. induction x. induction x.
 simpl in b1. induction b1. simpl. apply refl. Defined.

Definition Σ_equivalence_composition_forward  {A : Type} {P : A -> Type} (z w : Σ A P):
 (Σ_equivalence_backward z w) ∘ (Σ_equivalnce_forward z w) ~ (id _).
 intro x. induction x. simpl. induction x. simpl. unfold Σ_equivalnce_forward.
 simpl. apply refl. Defined. 

Definition isequiv_Σ_equivalence {A : Type} {P : A -> Type} (z w : Σ A P) :
 isequiv (Σ_equivalnce_forward z w).
 split. - exact (deppair _ _ (Σ_equivalence_backward z w) (Σ_equivalence_composition_backward z w)). 
 - exact (deppair _ _ (Σ_equivalence_backward z w) (Σ_equivalence_composition_forward z w)). Defined.



Definition Σ_equivalnce {A : Type} {P : A -> Type} (z w : Σ A P) : 
    (z ≡ w) ≃ Σ (proj1 z ≡ proj1 w) (fun p => (transport p (proj2 z)) ≡ (proj2 w)
     ).
     unfold equivalent.
     exact (deppair _ _ (Σ_equivalnce_forward z w) (isequiv_Σ_equivalence z w) ). Defined.

Definition Frob {A : Type} {x y: A} {p : x ≡ y} {C : forall (x y : A), (x ≡ y) -> Type -> Type} {Δ : forall (x y : A),  (x ≡ y) -> Type} :
    (Δ x x (refl x)) -> (C x x (refl x) (Δ x x (refl x))) -> (C x y p (Δ x y p)).
intro z_refl. intro d_refl. induction p. exact d_refl. Defined.

Definition fun_extention_Σ  {A: Type} {B C : A -> Type} (f : forall x : A, B x -> C x): (Σ A B) -> (Σ A C).
intro w. induction w. apply (deppair A C x (f x b)). Defined.

Definition dep_fun_inv {A : Type} {B C : A -> Type} (f : forall (x : A), B x -> C x) {p : forall (x : A), isequiv (f x)}:
forall (x : A), C x -> B x.
intro x. unfold isequiv in p. exact (proj1( pr1 (p x)) ). Defined.

Definition dep_fun_inv_2 {A : Type} {B C : A -> Type} (f : forall (x : A), B x -> C x) {p : forall (x : A), isequiv (f x)}:
forall (x : A), C x -> B x.
intro x. unfold isequiv in p. exact (proj1( pr2 (p x)) ). Defined.

Definition Dold_Theorem {A : Type} {B C : A -> Type} {f : forall (x : A), B x -> C x} {p : forall (x : A), isequiv (f x)} : 
Σ A B ≃ Σ A C.
unfold equivalent.
assert (  forall (w : Σ A C), ( (fun_extention_Σ f) ∘  ( @fun_extention_Σ (A) (C) (B) (@dep_fun_inv A B C f p) ) ) w 
                                                                                        ≡ (id (Σ A C)) w)  as H1.
- intro w. induction w. unfold composition. simpl. unfold id. unfold dep_fun_inv. unfold isequiv in p. unfold composition in p.
unfold id in p. 
apply (@ap _ _ (deppair A C x) (f x (proj1 (pr1 (p x)) b))  (b) ). apply ((proj2 (pr1 (p x))) b).
-  assert (  forall (w : Σ A B), ( ( @fun_extention_Σ (A) (C) (B) (@dep_fun_inv_2 A B C f p) ) ∘ (fun_extention_Σ f) ) w 
                                                                                                        ≡ (id (Σ A B)) w)  as H2.
+ intro w. induction w. unfold composition. simpl. unfold id. unfold dep_fun_inv. unfold isequiv in p. unfold composition in p.
unfold id in p. unfold dep_fun_inv_2.
apply (@ap _ _ (deppair A B x) ((proj1 (pr2 (p x)) (f x b)))). apply ((proj2 (pr2 (p x))) b).
+ unfold isequiv. 
apply (      
  deppair (Σ A B -> Σ A C) (fun f0 : Σ A B -> Σ A C => isequiv f0) (fun_extention_Σ f) 
    (pair _ _  (deppair (Σ A C -> Σ A B) (fun g : Σ A C -> Σ A B => (fun_extention_Σ f) ∘ g ~ id (Σ A C))  
              ( @fun_extention_Σ (A) (C) (B) (@dep_fun_inv A B C f p) ) H1 )
           
           (deppair (Σ A C -> Σ A B) (fun g : Σ A C -> Σ A B => g ∘ (fun_extention_Σ f) ~ id (Σ A B))
            ( @fun_extention_Σ (A) (C) (B) (@dep_fun_inv_2 A B C f p) ) H2)       )
).
Defined.

Definition check_unit (x y : unit): x ≡ y. 
induction x. induction y. apply refl.


Definition demorgan_1b (P Q : Type): ((P -> empty)  ×  (Q -> empty )) -> ((CoProd P Q) -> empty) :=
   fun f => fun c => 
     match c with 
       | inl _ _ p => (pr1 f) p
       | inr _ _ q => (pr2 f) q 
     end. Defined.


Definition mul_zero (m : nat) : m * 0 ≡ 0.
induction m.
- simpl. apply refl.
- simpl.
apply IHm.
Defined.

Inductive W (A : Type) (B : A -> Type) : Type :=
| sup (a : A): B(a) -> W A B. 

Definition constr_N_W : bool -> Type.
intro x. induction x.
- exact empty.
- exact unit.
Defined.


Definition N_W : Type.
exact (W bool constr_N_W). Defined.



Definition funext_conv (A B : Type) (f g: A -> B) : forall (x  : A), (( f x ≡ g x -> empty) -> ((f ≡ g) -> empty)).
intro x. intro H. intro p. induction p. exact (H (@refl _ _ )). Defined. 


Axiom functional_extensionality_dep : forall {A} {B : A -> Type},
  forall (f g : forall x : A, B x),
  (forall x, f x = g x) -> f = g.


Inductive two : Type :=
| true
| false.



Definition switch : two -> two.
intro x. induction x. exact (false). exact (true). Defined.

Definition switch_gives_id :  two ≡ two.
apply refl. Defined.






  