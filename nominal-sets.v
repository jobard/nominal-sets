Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Arith.Peano_dec.
Require Import List.
Import ListNotations.

(*
Require Import Relations.
Require Import Setoid.
Require Import Morphisms.
*)

Set Implicit Arguments.

Structure group :=
  {
    group_obj :> Type;
    group_id : group_obj;
    group_inv : group_obj -> group_obj;
    group_op : group_obj -> group_obj -> group_obj;
    group_assoc : forall x y z, group_op (group_op x y) z = group_op x (group_op y z);
    group_left_id : forall x, group_op group_id x = x;
    group_right_id : forall x, group_op x group_id = x;
    group_left_inv : forall x, group_op (group_inv x) x = group_id;
    group_right_inv : forall x, group_op x (group_inv x) = group_id;
  }.

Notation "1" := (group_id _).
Notation "x ^-1" := (group_inv _ x) (at level 30, format "x ^-1").
Notation "x * y" := (group_op _ x y).

Lemma group_inv_unique (G: group) (g h: G) : g * h = 1 -> g^-1 = h.
Proof.
  intros H. rewrite <- (group_right_id _ (g^-1)). rewrite <- H, <- group_assoc.
  now rewrite group_left_inv, group_left_id.
Qed.

Lemma group_inv_id (G: group) : 1^-1 = (group_id G).
Proof.
  apply group_inv_unique. now apply group_left_id.
Qed.

Lemma group_inv_op (G: group) (g h: G) : (g * h)^-1 = h^-1 * g^-1.
Proof.
  apply group_inv_unique. rewrite group_assoc, <- (group_assoc _ h).
  rewrite group_right_inv, group_left_id. now apply group_right_inv.
Qed.

Structure homomorphism :=
  {
    group_source : group;
    group_target : group;
    hom : group_source -> group_target;
    hom_id: hom 1 = 1;
    hom_op: forall x y, hom (x * y) = (hom x) * (hom y);
    hom_inv: forall x, hom (x^-1) = (hom x)^-1;
  }.

Structure G_set (G: group) :=
  {
    G_set_X :> Type;
    action: G -> G_set_X -> G_set_X;
    G_set_id: forall x,  (action 1 x) = x;
    G_set_assoc: forall g h x, (action g (action h x)) = (action (g * h) x);
  }.

Notation "g ** x" := (action _ g x) (at level 45, right associativity).

Ltac gsimpl :=
  repeat progress rewrite ?group_left_id, ?group_right_id, ?group_left_inv, ?group_right_inv,
  ?group_inv_id, ?group_inv_op,
  ?G_set_id, ?G_set_assoc.

Definition equivariant_func (G: group) (X Y: G_set G) (F: X -> Y) (x: X) (g: G) :=
  F (g ** x) = g ** F x.
  
Definition prod_action (G: group) (X Y: G_set G) (g: G) (p: X * Y) : X * Y :=
  match p with
  | (x, y) => (g ** x, g ** y)
  end.

Arguments prod_action {G X Y}.

Canonical Structure cartesian_prod (G: group) (X Y: G_set G) : G_set G.
apply (@Build_G_set G (X * Y)%type prod_action).
- intros [x y]. cbn. now gsimpl.
- intros g h [x y]. cbn. now gsimpl.
Defined.


Definition union_action (G: group) (X Y: G_set G) (g: G) (s: X + Y) : X + Y :=
  match s with
  | inl x => inl (g ** x)
  | inr y => inr (g ** y)
  end.

Arguments union_action {G X Y}.

Canonical Structure disjoint_union (G: group) (X Y: G_set G) : G_set G.
apply (@Build_G_set G (X + Y) union_action).
- intros [x|y]; cbn; now gsimpl.
- intros g h [x|y]; cbn; now gsimpl.
Defined.

Definition func_action (G: group) (X Y: G_set G) (g: G) (F: X -> Y) : X -> Y :=
  fun x => g ** F (g ^-1 ** x).

Arguments func_action {G X Y}.

Axiom func_eq : forall (G: group) (X Y: G_set G) (F1 F2: X -> Y), (forall (x: X), F1 x = F2 x) -> F1 = F2.

Canonical Structure func (G: group) (X Y: G_set G) : G_set G.
apply (@Build_G_set G (X -> Y) func_action).
- intros F. unfold func_action. apply func_eq. intros x. now gsimpl.
- intros g h F. eapply func_eq. unfold func_action. intros x. now gsimpl.
Defined.

Definition equivariant_subset (G: group) (X: G_set G) (P: X -> Prop) :=
  forall g x, P x -> P (g ** x).

Definition atom := nat.

Structure perm :=
  {
    perm_f:> atom -> atom;
    perm_g: atom -> atom;
    perm_right_inv: forall a, perm_f (perm_g a) = a;
    perm_left_inv: forall a, perm_g (perm_f a) = a;
  }.

Definition perm_id : perm.
apply (@Build_perm (@id atom) (@id atom)); intros a; reflexivity.
Defined.

Definition perm_inv (pi: perm) : perm.
destruct pi as [f g H1 H2]. apply (Build_perm g f H2 H1). 
Defined.

Definition perm_op (pi pi': perm) : perm.
destruct pi as [f g H1 H2]. destruct pi' as [f' g' H3 H4].
apply (Build_perm (compose f f') (compose g' g)).
- intros a. unfold compose. now rewrite H3, H1.
- intros a. unfold compose. now rewrite H2, H4.
Defined.

Axiom perm_eq : forall (pi pi': perm), (forall a, pi a = pi' a) -> pi = pi'.

Canonical Structure group_perm : group.
apply (@Build_group _ perm_id perm_inv perm_op).
- intros pi1 pi2 pi3. apply perm_eq. intros a. destruct pi1, pi2, pi3. unfold perm_op.
  cbn. now rewrite compose_assoc.
- intros pi. apply perm_eq. intros a. destruct pi. unfold perm_op. cbn.
  now rewrite compose_id_left.
- intros pi. apply perm_eq. intros a. destruct pi. unfold perm_op. cbn.
  now rewrite compose_id_right.
- intros pi. apply perm_eq. intros a. destruct pi. unfold perm_op. cbn.
  unfold id, compose. auto.
- intros pi. apply perm_eq. intros a. destruct pi. unfold perm_op. cbn.
  unfold id, compose. auto.
Defined.

Definition fin_perm (pi: perm) := exists l, forall a, ~ In a l -> pi a = a.

Definition transposition (pi: perm) := exists a, forall b, a <> b -> pi b = b.

Lemma fin_perm_transposition (pi: perm) : transposition pi -> fin_perm pi.
Proof.
  intros [a H]. exists [a]. intros x H'. apply H. intros E. rewrite E in H'. apply H'. now constructor.
Qed.

(* TODO: need fin_perm instead of perm? *)
Definition support (X: G_set group_perm) (A: atom -> Prop) (x: X) :=
  forall (pi: perm), (forall a, A a -> pi a = a) -> pi ** x = x.

Definition fin_pred (A: atom -> Prop) := exists l, forall a, A a ->  In a l.

Definition nominal (X: G_set group_perm) := forall x, exists2 A, support X A x & fin_pred A.

Definition supp (X: G_set group_perm) x := fun a => forall A, support X A x -> A a.

Definition perm_action (pi: perm) a := pi a.

Canonical Structure G_set_atom : G_set group_perm.
apply (@Build_G_set group_perm atom perm_action).
- intros a. now cbn.
- intros g h x. now destruct g, h.
Defined.

Lemma nominal_atom : nominal G_set_atom.
Proof.
  intros a. exists (fun x => x = a).
  - intros pi H. now apply H.
  - exists [a]. intros x E. now constructor.
Qed.

Lemma supp_func (X Y: G_set group_perm) (A: atom -> Prop) (F: X -> Y) :
  support _ A F <-> forall (pi: perm), (forall a, A a -> pi a = a) -> forall x, F (pi ** x) = pi ** F x.
Proof.
  split; intros H.
  - intros pi H' x. specialize (H pi H').
    assert (E: F (pi ** x) = (pi ** F) (pi ** x)) by now rewrite H.
    rewrite E. cbn. unfold func_action. now gsimpl.
  - intros pi H'. specialize (H (pi^-1)). apply func_eq. intros x. cbn. unfold func_action.
    rewrite H; gsimpl; auto. intros a Aa. specialize (H' a Aa). destruct pi as [pi pi' Hpi Hpi'].
    cbn. cbn in H'. now rewrite <- H' at 1.
Qed.
